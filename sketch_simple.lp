///////////////////////////////////////////////////////////////////////////////
// sketch_simple.lp — minimal cubical core: paths decided by the e-graph `when`.
// NO `theory`/canonizer, NO faces — just the two endpoints i0, i1.
// Design log / reasoning: see sketch_simple.context.
//
// THIS FILE CHECKS.  Run it from a package dir (e.g. copy under tests/):
//     LP_EGRAPH=1 lambdapi check tests/sketch_simple.lp        // all asserts pass
//     lambdapi check tests/sketch_simple.lp                    // boundary assert FAILS
//     LP_EGRAPH=1 LP_EGRAPH_PRINT=1 …                          // show the e-classes
//
// Matches cubical Agda: dependent paths PathP, ⟨i⟩ as path abstraction, `⋅` as
// path application with the endpoint COMPUTATION  p ⋅ i0 ≡ x  (IApply /
// reduceIApply boundary), and path-η.  The non-orientable equations (boundary,
// η) are `when` typed-constraints, merged into a GROUND e-graph and consulted
// from conversion when rewriting alone fails.
//
// Universe à la Tarski (U, El): a line of types is `H : I → U`, NOT `I → TYPE`.
// `I → U : TYPE`, so H is term-level and PathP sort-checks; `I → TYPE : KIND`
// would make PathP quantify over a kind, which Lambdapi rejects.
//
// Ground-CC: under binders, bound vars are SKOLEMIZED (de Bruijn indices), so
// merged equations are ground ⇒ conversion is decidable congruence closure.
// The e-graph "lives inside binders": interning saturates each scope — firing
// the `when`s on every typed subterm — and CONGRUENCE alone propagates the
// merged bodies up through λ and application heads (single class query).
///////////////////////////////////////////////////////////////////////////////

// Interval — the free De Morgan algebra on two endpoints.
symbol I  : TYPE;
symbol i0 : I;
symbol i1 : I;

// connections ∧ ∨ and reversal ~.  The ORIENTABLE fragment of the De Morgan
// laws is plain rewriting: endpoint folding, idempotence, involution, and the
// De Morgan pushes (~ inward).  Commutativity/associativity/distributivity are
// NOT included — they are non-orientable AND beyond ground congruence closure
// (AC needs the `theory` canonizer, out of scope here); closed interval terms
// all fold to i0/i1 anyway, so only ac-REARRANGED OPEN terms are undecided.
symbol ∧ : I → I → I;  notation ∧ infix left 20;
symbol ∨ : I → I → I;  notation ∨ infix left 15;
symbol ~ : I → I;      notation ~ prefix 30;

rule _ ∧ i0 ↪ i0    with i0 ∧ _ ↪ i0
with $i ∧ i1 ↪ $i   with i1 ∧ $i ↪ $i
with $i ∧ $i ↪ $i;                                   // idempotence (non-linear)
rule _ ∨ i1 ↪ i1    with i1 ∨ _ ↪ i1
with $i ∨ i0 ↪ $i   with i0 ∨ $i ↪ $i
with $i ∨ $i ↪ $i;
rule ~ i0 ↪ i1      with ~ i1 ↪ i0
with ~ (~ $i) ↪ $i;                                  // involution
rule ~ ($i ∧ $j) ↪ (~ $i) ∨ (~ $j);                  // De Morgan (push ~ inward)
rule ~ ($i ∨ $j) ↪ (~ $i) ∧ (~ $j);

///////////////////////////////////////////////////////////////////////////////
// Universe of codes (Tarski). `U` codes small types; `El` decodes. `pi` codes
// Π-types — needed because funext's endpoints are FUNCTIONS, so its line of
// types `λ i, Π x, …` must itself live in `I → U`.
///////////////////////////////////////////////////////////////////////////////
symbol U  : TYPE;                                    // codes for (small) types
// INJECTIVE so unification may decompose  El a ≡ El b  to  a ≡ b  (needed to
// solve ipath's implicit line H in infer mode; standard for Tarski encodings).
injective symbol El : U → TYPE;                      // decoding
symbol pi : Π (a : U), (El a → U) → U;               // code for Π-types
rule El (pi $a $b) ↪ Π (x : El $a), El ($b x);

///////////////////////////////////////////////////////////////////////////////
// Dependent paths. PathP H x y : a path in the LINE of codes H : I → U,
// from x : El (H i0) to y : El (H i1). Non-dependent Path is the constant line.
// INJECTIVE: `PathP … ≡ PathP ?H ?x ?y` decomposes, so `⋅`'s implicit H is
// solvable and the bare infix `p ⋅ e` elaborates (else ?H i0 ≡ A is a
// non-Miller higher-order problem and unification parks it).
///////////////////////////////////////////////////////////////////////////////
injective symbol PathP : Π (H : I → U), El (H i0) → El (H i1) → TYPE;
symbol Path : Π (a : U), El a → El a → TYPE;         // Path a ≔ PathP (λ _, a)
rule Path $a $x $y ↪ PathP (λ _, $a) $x $y;

// a CODE for path types — so a SQUARE (a path of paths) has a line in U:
symbol path : Π (a : U), El a → El a → U;
rule El (path $a $x $y) ↪ Path $a $x $y;

// application — p ⋅ e : El (H e)  (eliminator; `@` is RESERVED in LP, so `⋅`).
// H x y are implicit so the infix takes just the two operands `p ⋅ e`:
symbol ⋅ : Π [H : I → U] [x : El (H i0)] [y : El (H i1)],
           PathP H x y → Π (e : I), El (H e);
notation ⋅ infix 10;

// ⟨i⟩ t — path abstraction IS just an interval lambda: an ordinary symbol over
// the interior  Π (i : I), El (H i),  written with quantifier notation, so
//     ⟨i⟩ t   ≔   `ipath i, t   =   ipath (λ i, t).
// Endpoints x y are implicit: in CHECK mode they are read off the expected
// PathP type (the PathP-I rule below); in infer mode the assert's own typing
// constraint solves them through injective PathP.
//     Γ, i:I ⊢ t : El (H i)      t[i0/i] ≡ x      t[i1/i] ≡ y
//     ───────────────────────────────────────────────────────  (PathP-I)
//                   Γ ⊢ (⟨i⟩ t) : PathP H x y
symbol ipath : Π [H : I → U] [x : El (H i0)] [y : El (H i1)],
               (Π (i : I), El (H i)) → PathP H x y;
notation ipath quantifier;

// refl — the constant path, definable already:  refl t ≔ ⟨_⟩ t.
symbol refl : Π [a : U] (t : El a), Path a t t ≔ λ a t, `ipath _, t;

// β — dimension substitution (ORIENTABLE ⇒ a plain rewrite rule, not a `when`):
//     (⟨i⟩ F) ⋅ e  ↪  F e
rule @⋅ _ _ _ (@ipath _ _ _ $F) $e ↪ $F $e;

// boundary — endpoint COMPUTATION (cubical Agda's IApply); NON-orientable as a
// rule set (it is type-directed), so a `when`, keyed on `⋅`. `@⋅ $H $x $y`
// makes ⋅'s implicits EXPLICIT so the equations tie them to $p's type (plain
// `$p ⋅ i0` would leave H a metavar ⇒ ill-typed constraint):
when ⋅ $p : PathP $H $x $y
   ⊢ @⋅ $H $x $y $p i0 ≡ $x
   ⊢ @⋅ $H $x $y $p i1 ≡ $y;

// path-η — TYPE-keyed on `PathP` (the head qid IS the type former), eager:
// BUILD ⟨i⟩ (p ⋅ i) and merge (no HO matching anywhere). The λ domain is
// explicit — the equation must be hole-free to enter the ground graph.
when PathP $p : PathP $H $x $y
   ⊢ @ipath $H $x $y (λ (i : I), @⋅ $H $x $y $p i) ≡ $p;

///////////////////////////////////////////////////////////////////////////////
// Demonstrations — ground subjects ⇒ decided by ground congruence closure.
///////////////////////////////////////////////////////////////////////////////
symbol A : U; symbol t : El A; symbol u : El A; symbol p : Path A t u;
symbol i : I;                            // an opaque interval point (a symbol)

assert ⊢ p ⋅ i0 ≡ t;                     // boundary (endpoint computation)
assert ⊢ p ⋅ i1 ≡ u;                     // boundary
assert ⊢ (`ipath i, (p ⋅ i)) ≡ p;        // η
assertnot ⊢ p ⋅ i0 ≡ u;                  // no spurious merges: t ≢ u

// η where it matters — inside TYPE-CHECKING, not an assert: wit : P p is
// accepted at P (⟨i⟩ (p ⋅ i)) because conversion consults the graph.
symbol P : Path A t u → TYPE;
symbol wit : P p;
symbol useEta : P (`ipath i, (p ⋅ i)) ≔ wit;

// --- a constraint fired INSIDE a binder ---------------------------------------
// h x : Path A x x has a type mentioning the BOUND x, so checking
//     λ x, (h x) ⋅ i0  ≡  λ x, x
// needs the boundary AT x: interning saturates the λ-scope (fires the `when`
// on h x keyed at x's index) and congruence collapses the bodies, the λs, the Qs.
symbol h : Π (x : El A), Path A x x;
symbol Q : (El A → El A) → TYPE;
symbol qwit : Q (λ x, x);
symbol useBinder : Q (λ x, (h x) ⋅ i0) ≔ qwit;

// --- function extensionality (dependent) — the headline. ----------------------
// B x : I → U is a line of codes per point x; f, g are its two endpoints.
// Uses ONLY path-β + the boundary `when` (fired on `funext hpt` itself, whose
// snf through path-β is  λ x, hpt x ⋅ i0  — exactly the queried form).
symbol B : El A → I → U;
symbol f : Π (x : El A), El (B x i0);
symbol g : Π (x : El A), El (B x i1);
symbol hpt : Π (x : El A), PathP (B x) (f x) (g x);  // pointwise dependent path
symbol funext :
  (Π (x : El A), PathP (B x) (f x) (g x)) → PathP (λ i, pi A (λ x, B x i)) f g;
rule funext $h ↪ `ipath i, (λ x, ($h x) ⋅ i);

assert ⊢ ((funext hpt) ⋅ i) t ≡ (hpt t) ⋅ i;         // pointwise computation, pure β

// the two boundary FACES — i substituted FIRST ⇒ two DISTINCT equations against
// two DISTINCT endpoints (never one `λ x, hpt x ⋅ i ≡ f ≡ g`):
//   i:=i0:  (funext hpt) ⋅ i0 = λ x, (hpt x) ⋅ i0    (path-β)
//                             ≡ f                     (boundary on funext hpt)
assert ⊢ (funext hpt) ⋅ i0 ≡ f;
assert ⊢ (funext hpt) ⋅ i1 ≡ g;                       //   i:=i1:  … ≡ g

// --- interval structure at work: symmetry and connections ---------------------
// symmetry — reversal:  sym p ≔ ⟨i⟩ p ⋅ ~i.
symbol sym : Π [a : U] [x : El a] [y : El a], Path a x y → Path a y x
  ≔ λ a x y p, `ipath i, (p ⋅ (~ i));

// A ground-typed alias: `(sym p) ⋅ i0` directly would stack sym's THREE implicit
// metas on ⋅'s implicit H and the unifier parks `?H i0 ≡ ?a` (non-Miller) — a
// pre-existing elaboration-order weakness, orthogonal to the e-graph.  Checking
// `sym p` against a ground type solves its implicits first.
symbol symp : Path A u t ≔ sym p;

assert ⊢ symp ⋅ i0 ≡ u;                  // ~i0 folds to i1, then boundary
assert ⊢ symp ⋅ i1 ≡ t;
// double reversal:  snf gives  ⟨i⟩ p ⋅ ~~i  ↪(involution)  ⟨i⟩ p ⋅ i  ≡(η)  p
assert ⊢ sym symp ≡ p;

// ∧-connection — the square  cAnd i j ≔ p ⋅ (i ∧ j),
//     j:  x ── p ── u          faces:  i:=i0 ⇒ ⟨j⟩ p⋅i0     ≡ refl t
//     ↑   .         .                  i:=i1 ⇒ ⟨j⟩ p⋅j      ≡ p  (η)
//     x ── refl ──── x  →i             (folding does i0∧j ↪ i0, i1∧j ↪ j)
// Even TYPING it needs the graph: the declared endpoints are (refl t) and p,
// so elaboration must convert  p ⋅ i0 ≡ t  inside the type's line.
symbol cAnd : PathP (λ i, path A t (p ⋅ i)) (refl t) p
  ≔ `ipath i, `ipath j, (p ⋅ (i ∧ j));

assert ⊢ cAnd ⋅ i0 ≡ refl t;             // bottom face
assert ⊢ cAnd ⋅ i1 ≡ p;                  // top face (η after i1∧j ↪ j)

// ∨-connection — the mirrored square:  faces  i:=i0 ⇒ p,  i:=i1 ⇒ refl u.
symbol cOr : PathP (λ i, path A (p ⋅ i) u) p (refl u)
  ≔ `ipath i, `ipath j, (p ⋅ (i ∨ j));

assert ⊢ cOr ⋅ i0 ≡ p;
assert ⊢ cOr ⋅ i1 ≡ refl u;

// KNOWN LIMIT (needs the AC `theory` canonizer, not ground CC): commuted open
// terms like  ⟨i⟩⟨j⟩ p ⋅ (i ∧ j)  vs  ⟨i⟩⟨j⟩ p ⋅ (j ∧ i)  are equal in the De
// Morgan algebra but undecided here — no assert.

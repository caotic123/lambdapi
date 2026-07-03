// Consistency probes: with the e-graph ON, everything DISTINCT must STAY
// distinct (assertnot).  Any failure here = an over-merge = unsoundness.
symbol I : TYPE; symbol i0 : I; symbol i1 : I;
symbol ∧ : I → I → I;  notation ∧ infix left 20;
symbol ∨ : I → I → I;  notation ∨ infix left 15;
symbol ~ : I → I;      notation ~ prefix 30;
rule _ ∧ i0 ↪ i0    with i0 ∧ _ ↪ i0
with $i ∧ i1 ↪ $i   with i1 ∧ $i ↪ $i
with $i ∧ $i ↪ $i;
rule _ ∨ i1 ↪ i1    with i1 ∨ _ ↪ i1
with $i ∨ i0 ↪ $i   with i0 ∨ $i ↪ $i
with $i ∨ $i ↪ $i;
rule ~ i0 ↪ i1      with ~ i1 ↪ i0
with ~ (~ $i) ↪ $i;
rule ~ ($i ∧ $j) ↪ (~ $i) ∨ (~ $j);
rule ~ ($i ∨ $j) ↪ (~ $i) ∧ (~ $j);
symbol U : TYPE; injective symbol El : U → TYPE;
injective symbol PathP : Π (H : I → U), El (H i0) → El (H i1) → TYPE;
symbol Path : Π (a : U), El a → El a → TYPE;
rule Path $a $x $y ↪ PathP (λ _, $a) $x $y;
symbol path : Π (a : U), El a → El a → U;
rule El (path $a $x $y) ↪ Path $a $x $y;
symbol ⋅ : Π [H : I → U] [x : El (H i0)] [y : El (H i1)], PathP H x y → Π (e : I), El (H e);
notation ⋅ infix 10;
symbol ipath : Π [H : I → U] [x : El (H i0)] [y : El (H i1)], (Π (i : I), El (H i)) → PathP H x y;
notation ipath quantifier;
when ⋅ $q : PathP $H $x $y
   ⊢ @⋅ $H $x $y $q i0 ≡ $x
   ⊢ @⋅ $H $x $y $q i1 ≡ $y;
when PathP $q : PathP $H $x $y
   ⊢ @ipath $H $x $y (λ (i : I), @⋅ $H $x $y $q i) ≡ $q;

symbol A : U; symbol t : El A; symbol u : El A; symbol v : El A;
symbol p : Path A t u;
symbol q : Path A t u;                   // a SECOND path with the SAME endpoints
symbol r : Path A u v;                   // a path with DIFFERENT endpoints
symbol k : I;                            // opaque interval point

// ── the interval stays free ───────────────────────────────────────────────────
assertnot ⊢ i0 ≡ i1;
assertnot ⊢ ~ k ≡ k;
assertnot ⊢ k ∧ i0 ≡ i1;                 // folds to i0, must not equal i1

// ── endpoints: right ones, only the right ones ───────────────────────────────
assert    ⊢ p ⋅ i0 ≡ t;
assertnot ⊢ p ⋅ i0 ≡ u;                  // wrong endpoint
assertnot ⊢ p ⋅ i1 ≡ t;
assertnot ⊢ p ⋅ k  ≡ t;                  // interior point is NOT an endpoint
assertnot ⊢ t ≡ u;                       // boundary facts must not identify endpoints

// ── distinct paths stay distinct (even with EQUAL endpoints and types) ────────
assertnot ⊢ p ≡ q;
assert    ⊢ q ⋅ i0 ≡ t;                  // q gets ITS OWN boundary...
assertnot ⊢ p ⋅ k ≡ q ⋅ k;               // ...but interiors never merge

// ── no cross-path contamination ──────────────────────────────────────────────
assert    ⊢ r ⋅ i0 ≡ u;                  // r's boundary is r's
assertnot ⊢ r ⋅ i0 ≡ t;                  // not p's
assertnot ⊢ t ≡ v;                       // transitivity must not bridge p and r

// ── η merges the right things only ───────────────────────────────────────────
assert    ⊢ (`ipath i, (p ⋅ i)) ≡ p;
assertnot ⊢ (`ipath i, (p ⋅ i)) ≡ q;     // p's η-form is not q
assertnot ⊢ (`ipath i, (p ⋅ (~ i))) ≡ p; // the REVERSED path is not p

// ── congruence must not over-apply ───────────────────────────────────────────
symbol P : El A → TYPE;
assertnot ⊢ P t ≡ P u;
symbol h : Π (x : El A), Path A x x;
symbol Q : (El A → El A) → TYPE;
assert    ⊢ Q (λ x, (h x) ⋅ i0) ≡ Q (λ x, x);   // the sound under-binder merge
assertnot ⊢ Q (λ x, (h x) ⋅ i0) ≡ Q (λ _, t);   // but not to a constant map
assertnot ⊢ (λ x, (h x) ⋅ i0) ≡ (λ _, t);

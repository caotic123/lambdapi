// Checkable subset of sketch_simple.lp: the parts that need NEITHER the ⟨i⟩
// elaborator nor higher-order implicit solving.  Demonstrates the e-graph deciding
// the path-boundary equation DURING TYPE-CHECKING (conversion) — not only asserts.
// Run:  LP_EGRAPH=1 lambdapi check tests/sketch_egraph.lp

symbol I : TYPE; symbol i0 : I; symbol i1 : I;
symbol U : TYPE; symbol El : U → TYPE;
symbol pi : Π (a : U), (El a → U) → U;
rule El (pi $a $b) ↪ Π (x : El $a), El ($b x);
symbol PathP : Π (H : I → U), El (H i0) → El (H i1) → TYPE;
symbol Path  : Π (a : U), El a → El a → TYPE;
rule  Path $a $x $y ↪ PathP (λ _, $a) $x $y;
symbol ⋅ : Π [H : I → U] [x : El (H i0)] [y : El (H i1)], PathP H x y → Π (e : I), El (H e);
notation ⋅ infix 10;
when ⋅ $p : PathP $H $x $y
   ⊢ @⋅ $H $x $y $p i0 ≡ $x
   ⊢ @⋅ $H $x $y $p i1 ≡ $y;

symbol A : U; symbol t : El A; symbol u : El A; symbol p : Path A t u;

// (1) boundary as ASSERTS — not convertible by rewriting; decided by the e-graph.
assert ⊢ @⋅ (λ _, A) t u p i0 ≡ t;
assert ⊢ @⋅ (λ _, A) t u p i1 ≡ u;
// negative control: i0's boundary is t, not u — must stay non-convertible.
assertnot ⊢ @⋅ (λ _, A) t u p i0 ≡ u;

// (2) boundary INSIDE TYPE-CHECKING (conversion, the new capability): checking
// `wit : P t` at the declared type `P (@⋅ … i0)` forces  P t ≡ P (@⋅ … i0), i.e. the
// boundary `@⋅ … i0 ≡ t`, decided by the e-graph inside eq_modulo — no assert.
symbol P   : El A → TYPE;
symbol wit : P t;
symbol use : P (@⋅ (λ _, A) t u p i0) ≔ wit;

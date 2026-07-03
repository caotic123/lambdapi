// A constraint that must fire INSIDE a binder to unify: checking wit against
// P (λ x, (h x) ⋅ i0) needs  h x ⋅ i0 ≡ x  UNDER the λ — h x's type mentions
// the bound x, so no top-level fact can decide it.
symbol I : TYPE; symbol i0 : I; symbol i1 : I;
symbol U : TYPE; symbol El : U → TYPE;
injective symbol PathP : Π (H : I → U), El (H i0) → El (H i1) → TYPE;
symbol Path : Π (a : U), El a → El a → TYPE;
rule Path $a $x $y ↪ PathP (λ _, $a) $x $y;
symbol ⋅ : Π [H : I → U] [x : El (H i0)] [y : El (H i1)], PathP H x y → Π (e : I), El (H e);
notation ⋅ infix 10;
when ⋅ $q : PathP $H $x $y
   ⊢ @⋅ $H $x $y $q i0 ≡ $x
   ⊢ @⋅ $H $x $y $q i1 ≡ $y;

symbol A : U;
symbol h : Π (x : El A), Path A x x;      // a per-point loop: h x : Path A x x
symbol P : (El A → El A) → TYPE;
symbol wit : P (λ x, x);
// conversion goal:  λ x, (h x) ⋅ i0  ≡  λ x, x   — boundary under the binder.
symbol use : P (λ x, (h x) ⋅ i0) ≔ wit;

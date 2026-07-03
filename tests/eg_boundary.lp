// Stage-2 observation file: boundary `when` only, no η, no asserts.
// Run:  LP_EGRAPH=1 lambdapi check eg_boundary.lp
// Expect a "[egraph] … constraint-fires" line: the boundary fires on `p`.

symbol I  : TYPE;
symbol i0 : I;
symbol i1 : I;

symbol U  : TYPE;
symbol El : U → TYPE;
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

symbol A : U;
symbol t : El A;
symbol u : El A;
symbol p : Path A t u;

// NOT convertible by rewriting (⋅ is neutral); these hold only via the boundary
// `when` fired on `p`, decided by the e-graph consult.  (Explicit @⋅: bare
// `p ⋅ i0` can't elaborate the higher-order implicit H : I → U.)
assert ⊢ @⋅ (λ _, A) t u p i0 ≡ t;
assert ⊢ @⋅ (λ _, A) t u p i1 ≡ u;
// Negative control: i0's boundary is t, not u — must stay non-convertible.
assertnot ⊢ @⋅ (λ _, A) t u p i0 ≡ u;

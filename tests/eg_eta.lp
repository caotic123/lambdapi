symbol I : TYPE; symbol i0 : I; symbol i1 : I;
symbol U : TYPE; symbol El : U → TYPE;
symbol PathP : Π (H : I → U), El (H i0) → El (H i1) → TYPE;
symbol Path  : Π (a : U), El a → El a → TYPE;
rule  Path $a $x $y ↪ PathP (λ _, $a) $x $y;
symbol ⋅ : Π [H : I → U] [x : El (H i0)] [y : El (H i1)], PathP H x y → Π (e : I), El (H e);
notation ⋅ infix 10;
symbol ipath : Π [H : I → U] [x : El (H i0)] [y : El (H i1)], (Π (i : I), El (H i)) → PathP H x y;
// path-η with EXPLICIT domain λ (i:I) so no Plac reaches the graph:
when PathP $q : PathP $H $x $y
   ⊢ @ipath $H $x $y (λ (i : I), @⋅ $H $x $y $q i) ≡ $q;
symbol A : U; symbol t : El A; symbol u : El A; symbol p : Path A t u;
assert ⊢ @ipath (λ _, A) t u (λ (i : I), @⋅ (λ _, A) t u p i) ≡ p;

symbol I : TYPE; symbol i0 : I; symbol i1 : I;
symbol U : TYPE; symbol El : U → TYPE;
injective symbol PathP : Π (H : I → U), El (H i0) → El (H i1) → TYPE;
symbol ⋅ : Π [H : I → U] [x : El (H i0)] [y : El (H i1)], PathP H x y → Π (e : I), El (H e);
notation ⋅ infix 10;
symbol ipath : Π [H : I → U] [x : El (H i0)] [y : El (H i1)], (Π (i : I), El (H i)) → PathP H x y;
notation ipath quantifier;                      // ⟨i⟩ t  ≔  `ipath i, t  =  ipath (λ i, t)
symbol A : U; symbol t : El A; symbol u : El A;
symbol p : PathP (λ _, A) t u;
// (a) bare  p ⋅ i0  — implicit H, now that PathP is injective:
assert ⊢ p ⋅ i0 : El A;
// (b) path abstraction as lambda binder syntax, checked against p's type:
symbol test : PathP (λ _, A) t u ≔ `ipath i, (p ⋅ i);

// sketch_simple.lp, made checkable: ⟨i⟩ = interval-lambda (quantifier notation),
// PathP injective (fixes ⋅'s implicit), path equations decided by the e-graph.
symbol I : TYPE; symbol i0 : I; symbol i1 : I;
symbol U : TYPE; symbol El : U → TYPE;
symbol pi : Π (a : U), (El a → U) → U;
rule El (pi $a $b) ↪ Π (x : El $a), El ($b x);
injective symbol PathP : Π (H : I → U), El (H i0) → El (H i1) → TYPE;
symbol Path : Π (a : U), El a → El a → TYPE;
rule Path $a $x $y ↪ PathP (λ _, $a) $x $y;
symbol ⋅ : Π [H : I → U] [x : El (H i0)] [y : El (H i1)], PathP H x y → Π (e : I), El (H e);
notation ⋅ infix 10;
symbol ipath : Π [H : I → U] [x : El (H i0)] [y : El (H i1)], (Π (i : I), El (H i)) → PathP H x y;
notation ipath quantifier;                       // ⟨i⟩ t  ≔  `ipath i, t
// boundary + η, keyed on ⋅ and PathP:
when ⋅ $q : PathP $H $x $y
   ⊢ @⋅ $H $x $y $q i0 ≡ $x
   ⊢ @⋅ $H $x $y $q i1 ≡ $y;
when PathP $q : PathP $H $x $y
   ⊢ @ipath $H $x $y (λ (i : I), @⋅ $H $x $y $q i) ≡ $q;
symbol A : U; symbol t : El A; symbol u : El A; symbol p : Path A t u;

// boundary — bare infix, decided by the e-graph:
assert ⊢ p ⋅ i0 ≡ t;
assert ⊢ p ⋅ i1 ≡ u;

// η — ⟨i⟩ in lambda syntax (check mode reads the endpoints from P's arg type);
// checking wit:P p at P (`ipath i, p⋅i) needs  p ≡ ⟨i⟩(p⋅i), decided by the e-graph:
symbol P : Path A t u → TYPE;
symbol wit : P p;
symbol useEta : P (`ipath i, (p ⋅ i)) ≔ wit;

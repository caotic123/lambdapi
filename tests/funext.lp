// funext — the headline: pointwise paths → path of functions.
// Needs: path-β (rewrite), per-fibre boundary (when + e-graph UNDER a binder), fn-η.
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
notation ipath quantifier;
// path-β: (⟨i⟩ F) ⋅ e ↪ F e   (dimension substitution)
rule @⋅ _ _ _ (@ipath _ _ _ $F) $e ↪ $F $e;
// boundary (when):
when ⋅ $q : PathP $H $x $y
   ⊢ @⋅ $H $x $y $q i0 ≡ $x
   ⊢ @⋅ $H $x $y $q i1 ≡ $y;

symbol A : U;
symbol B : El A → I → U;                     // a line of codes per point x
symbol f : Π (x : El A), El (B x i0);
symbol g : Π (x : El A), El (B x i1);
symbol hpt : Π (x : El A), PathP (B x) (f x) (g x);   // pointwise dependent path
symbol funext :
  (Π (x : El A), PathP (B x) (f x) (g x)) → PathP (λ i, pi A (λ x, B x i)) f g;
rule funext $h ↪ `ipath i, (λ x, ($h x) ⋅ i);

symbol t : El A;
symbol i : I;                                 // opaque interval point
assert ⊢ ((funext hpt) ⋅ i) t ≡ (hpt t) ⋅ i;  // pointwise computation — pure β
assert ⊢ (funext hpt) ⋅ i0 ≡ f;               // face i0: needs per-fibre boundary + fn-η
assert ⊢ (funext hpt) ⋅ i1 ≡ g;               // face i1

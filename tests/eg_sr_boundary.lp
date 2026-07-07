// Subject reduction through the e-graph.  Run: LP_EGRAPH=1 lambdapi check.
//
// The boundary-respecting path constructor [ipath F : PathP H (F i0) (F i1)]
// makes rules like funext produce residual SR goals [f ≡ λ x, ($h x) ⋅ i0]
// that only the `when` boundary equations (plus η-alignment) can discharge:
// this file must FAIL if either Tool.Sr.unsolved_hook or the consult's
// η-alignment is broken, and the assertnots must FAIL on any over-merge.

symbol I : TYPE; symbol i0 : I; symbol i1 : I;
symbol U : TYPE; injective symbol El : U → TYPE;
symbol pi : Π (a : U), (El a → U) → U;
rule El (pi $a $b) ↪ Π (x : El $a), El ($b x);
injective symbol PathP : Π (H : I → U), El (H i0) → El (H i1) → TYPE;
symbol ⋅ : Π [H : I → U] [x : El (H i0)] [y : El (H i1)],
           PathP H x y → Π (e : I), El (H e);
notation ⋅ infix 10;
symbol ipath : Π [H : I → U] (F : Π (i : I), El (H i)), PathP H (F i0) (F i1);
notation ipath quantifier;
rule @⋅ _ _ _ (@ipath _ $F) $e ↪ $F $e;

when ⋅ $p : PathP $H $x $y
   ⊢ @⋅ $H $x $y $p i0 ≡ $x
   ⊢ @⋅ $H $x $y $p i1 ≡ $y;

// constant line, so wrong-face probes below are homogeneous (well-typed)
symbol A : U; symbol C : U;
symbol f : Π (_ : El A), El C;
symbol g : Π (_ : El A), El C;
symbol h : Π (x : El A), PathP (λ _, C) (f x) (g x);
symbol funext : (Π (x : El A), PathP (λ _, C) (f x) (g x))
              → PathP (λ _, pi A (λ _, C)) f g;
rule funext $h ↪ `ipath i, (λ x, ($h x) ⋅ i);   // SR goals discharged by graph

symbol t : El A; symbol k : I;
assert    ⊢ ((funext h) ⋅ k) t ≡ (h t) ⋅ k;     // pointwise: pure β
assert    ⊢ (funext h) ⋅ i0 ≡ f;                // face i0: boundary + η-align
assert    ⊢ (funext h) ⋅ i1 ≡ g;                // face i1
assertnot ⊢ (funext h) ⋅ i0 ≡ g;                // wrong face must stay distinct
assertnot ⊢ (funext h) ⋅ k  ≡ f;                // interior point is not a face
assertnot ⊢ f ≡ g;                              // η-align must not bridge them

// A rule whose body FORGES its endpoints is rejected in SR — the graph never
// merges distinct constants, so the hook cannot discharge [u ≡ v]:
//   symbol u : El C; symbol v : El C;
//   symbol bogus : PathP (λ _, C) u v;
//   rule bogus ↪ @ipath (λ _, C) (λ _, u);     // Cannot solve u ≡ v.

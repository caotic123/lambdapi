This experiments type constraints and how could be propagated by a non-confluent e-graph structure

```
when ⋅ $p : T                               // boundary (e-graph)
   ⊢ $p ≡ q
   ⊢ ...
```

We trigger every time there is a new judgment at Γ.
The e-graph saturates with the new type constraints and solves modulo rewriting and congruence.
This is a heavily dangerous feature (non-confluent rules are evil, termination based on these kinds of rules is hell, congruence should be proof-producing, not an oracle, nor should it be at the core) and quickly implemented, but it is curious how nice it was to implement. But there is something cool about having non-confluent rules, they allow to encode type contraints that would be painful without so.

```
// Minimal funext.  Run: LP_EGRAPH=1 lambdapi check examples/funext_min.lp

// interval
symbol I : TYPE; symbol i0 : I; symbol i1 : I;

// Tarski universe
symbol U : TYPE; injective symbol El : U → TYPE;
symbol pi : Π (a : U), (El a → U) → U;                    // code for Π
rule El (pi $a $b) ↪ Π (x : El $a), El ($b x);

// dependent paths
injective symbol PathP : Π (H : I → U), El (H i0) → El (H i1) → TYPE;

// path application and abstraction (⟨i⟩ t  is  `ipath i, t)
symbol ⋅ : Π [H : I → U] [x : El (H i0)] [y : El (H i1)],
           PathP H x y → Π (e : I), El (H e);
notation ⋅ infix 10;
symbol ipath : Π [H : I → U] [x : El (H i0)] [y : El (H i1)],
               (Π (i : I), El (H i)) → PathP H x y;
notation ipath quantifier;

rule @⋅ _ _ _ (@ipath _ _ _ $F) $e ↪ $F $e;               // path-β

when ⋅ $p : PathP $H $x $y                                 // boundary (e-graph)
   ⊢ @⋅ $H $x $y $p i0 ≡ $x
   ⊢ @⋅ $H $x $y $p i1 ≡ $y;

// funext: pointwise paths → path of functions
symbol A : U;
symbol B : El A → I → U;                                   // a line per point
symbol f : Π (x : El A), El (B x i0);
symbol g : Π (x : El A), El (B x i1);
symbol h : Π (x : El A), PathP (B x) (f x) (g x);          // pointwise path
symbol funext :
  (Π (x : El A), PathP (B x) (f x) (g x)) → PathP (λ i, pi A (λ x, B x i)) f g;
rule funext $h ↪ `ipath i, (λ x, ($h x) ⋅ i);

symbol t : El A; symbol i : I;
assert ⊢ ((funext h) ⋅ i) t ≡ (h t) ⋅ i;                   // pointwise: pure β
assert ⊢ (funext h) ⋅ i0 ≡ f;                              // face i0: e-graph
assert ⊢ (funext h) ⋅ i1 ≡ g;                              // face i1
```

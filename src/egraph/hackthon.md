This experiments type constraints and how could be propagated by a non-confluent e-graph structure

```
when ⋅ $p : T                               // boundary (e-graph)
   ⊢ $p ≡ q
   ⊢ ...
```

We trigger every time there is a new judgment at Γ.
The e-graph saturates with the new type constraints and solves modulo rewriting and congruence.
This is a heavily dangerous feature (non-confluent rules are evil, termination based on these kinds of rules is hell, congruence should be proof-producing, not an oracle, nor should it be at the core) and quickly implemented, but it is curious how nice it was to implement. But there is something cool about having non-confluent rules, they allow to encode type constraints that would be painful without so.

Since `when` equations are ASSERTED (merged), never checked, soundness demands
that canonical paths cannot lie about their endpoints: `ipath` pins them to the
faces of its body, `ipath F : PathP H (F i0) (F i1)`, exactly as in the cubical
typing rule for `⟨i⟩ t`.  (An endpoint-agnostic `ipath : … → PathP H x y` lets
`rule bogus ↪ @ipath _ u v (λ _, u)` pass subject reduction, after which the
boundary fire merges `u ≡ v` — conversion collapses.)  Two pieces make the
strong constructor livable:

- rule subject-reduction offers its residual goals to the graph
  (`Tool.Sr.unsolved_hook`, installed by `Handle.Eg_coord`): the SR goals of
  `funext $h ↪ ⟨i⟩ λ x, $h x ⋅ i` are `f ≡ λ x, ($h x) ⋅ i0` (and `i1`) with
  `$h` already a fresh ground symbol — precisely the `when` boundary equations;
- the consult η-ALIGNS a bare function against an abstraction
  (`f` vs `λ x, t` becomes `λ x, f x` vs `λ x, t`) since the graph itself is
  snf-first structural congruence, with no η.

A forged-endpoint rule still dies in SR (`Cannot solve u ≡ v`): the graph has
no equation merging distinct constants, so the hook cannot discharge it.

Minimal example of native and computational function extensionality

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
symbol ipath : Π [H : I → U] (F : Π (i : I), El (H i)), PathP H (F i0) (F i1);
notation ipath quantifier;

rule @⋅ _ _ _ (@ipath _ $F) $e ↪ $F $e;                   // path-β

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

## Typing derivation of the `funext` rule

Subject reduction must show the RHS inhabits the LHS type.  Abbreviations:
`Ĥ ≔ λ i, pi A (λ x, B x i)` (the line of function types), `h̄` the fresh
symbol SR substitutes for the pattern variable `$h` (printed `$1`),
`F ≔ λ (i : I) (x : El A), (h̄ x) ⋅ i` (the RHS path body), and
`Γ ≔ i : I, x : El A`.  `≡` is conversion (β + rewrite rules), `≈` an
e-class equality in the graph.

The LHS types as `funext h̄ : PathP Ĥ f g` — the type the RHS must match.

`𝒟_F` — the path body (pure `Infer`, no e-graph):

```
  h̄ : Π (x : El A), PathP (B x) (f x) (g x)        x ∈ Γ
  ──────────────────────────────────────────────────────── app
  Γ ⊢ h̄ x : PathP (B x) (f x) (g x)                            i ∈ Γ
  ─────────────────────────────────────────────────────────────────── app-⋅  [H ≔ B x, x ≔ f x, y ≔ g x]
  Γ ⊢ (h̄ x) ⋅ i : El (B x i)
  ──────────────────────────────────────────────────────── abst
  i : I ⊢ λ x, (h̄ x) ⋅ i : Π (x : El A), El (B x i)
  ════════════════════════════════════════════════════════ conv:  El (Ĥ i) ↪β El (pi A (λ x, B x i)) ↪El-pi Π (x : El A), El (B x i)
  i : I ⊢ λ x, (h̄ x) ⋅ i : El (Ĥ i)
  ──────────────────────────────────────────────────────── abst
  ⊢ F : Π (i : I), El (Ĥ i)
```

Root — the RHS against the LHS type:

```
                    𝒟_F
  ─────────────────────────────────── ipath  [H ≔ Ĥ]
  ⊢ ipath F : PathP Ĥ (F i0) (F i1)
  ═══════════════════════════════════ conv, PathP injective
  ⊢ ipath F : PathP Ĥ f g             residual goals:   G₀ : F i0 ≡ f     G₁ : F i1 ≡ g
```

Unification cannot solve `G₀`/`G₁` — β only reaches `F i0 ↪ λ x, (h̄ x) ⋅ i0`,
and nothing rewrites that to `f`.  `Sr.check_rule` hands them to the graph
(`Tool.Sr.unsolved_hook` → `Eg_coord.consult`), which closes them:

```
  Γ ⊢ h̄ x : PathP (B x) (f x) (g x)                        ⌐ subject synthesized by saturate,
  ─────────────────────────────────── when (boundary fire)  ¦ UNDER the binder, equations keyed
  E₀ : (h̄ x) ⋅ i0 ≈ f x                                    ¦ at the occurrence's de Bruijn env
  ─────────────────────────────────── congruence (Abst over equal body classes)
  λ x, (h̄ x) ⋅ i0 ≈ λ x, f x            f ≈ λ x, f x   (η-align)
  ────────────────────────────────────────────────────────────── transitivity
  λ x, (h̄ x) ⋅ i0 ≈ f                                       ⟹ G₀ discharged   ∎
```

`G₁` is symmetric via `E₁ : (h̄ x) ⋅ i1 ≈ g x`.  Machinery map: `app`/`abst`/
`conv` are `Core.Infer`; the residual goals are parked by `Core.Unif` and
collected in `Tool.Sr.check_rule`; the boundary fire is `Egraph.saturate`/
`fire`; η-alignment is `Eg_coord.eta_align`; the final step is ego's
congruence closure.  The face asserts (`(funext h) ⋅ i0 ≡ f`) discharge by the
SAME tree with the declared `h` in place of `h̄`, after `funext h ⋅ i0` reduces
to `λ x, (h x) ⋅ i0` by the rule + path-β.

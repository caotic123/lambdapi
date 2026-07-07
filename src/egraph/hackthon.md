# Type constraints through an e-graph

This is a small experiment: let the type checker learn equations from typing
judgments — not only from rewrite rules — and decide conversion with an
e-graph (congruence closure) on top of ordinary rewriting.

```
when ⋅ $p : T                               // boundary (e-graph)
   ⊢ $p ≡ q
   ⊢ ...
```

Every time the checker derives a judgment whose type matches the guard, the
listed equations are merged into the graph, unoriented.  Conversion first
normalises as usual; when that is not enough, it asks the graph whether the
two sides ended up in the same class.

A word of caution before the fun: this is a dangerous toy.  Non-confluent
rules are evil, termination arguments around them are hell, and a congruence
oracle should really produce proofs rather than be trusted at the core.  It
was, however, surprisingly pleasant to build — and there is something cool
here: unoriented equations can express type constraints that rules alone
cannot.

## Keeping it sound

`when` equations are asserted, never checked.  So the constructors must make
them true on canonical forms.  For paths this means `ipath` cannot lie about
its endpoints: they are pinned to the faces of its body,

```
ipath F : PathP H (F i0) (F i1)
```

exactly the cubical typing rule for `⟨i⟩ t`.  (With an endpoint-agnostic
`ipath : … → PathP H x y`, one bogus rule is enough to merge two distinct
constants — and conversion collapses.)  Two things make the honest
constructor comfortable to use:

- when checking that a rule preserves typing gets stuck on a goal, the goal
  is offered to the graph — for `funext` those goals are precisely the
  boundary equations;
- the graph has no η of its own, so when a bare function meets an
  abstraction (`f` against `λ x, t`) the function is η-expanded first
  (`λ x, f x`), and congruence on the bodies does the rest.

A rule that forges its endpoints still dies with `Cannot solve u ≡ v`:
nothing in the graph merges two distinct constants, so there is no way to
discharge it.

## Warm-up: η-laws (`examples/eta_min.lp`)

The simplest type-directed equalities, well below paths.

Unit-η — `u ≡ tt` for every `u : Unit` — cannot even be written as a rule:
its left-hand side would be a bare variable.  On a neutral `u` there is no
syntax to match; only the type knows.

Surjective pairing — `pair (fst p) (snd p) ≡ p` — can be written as a rule,
but a treacherous one: it fires only while its two copies of `p` are
literally the same term, and any step inside one copy breaks the match.  All
its critical pairs join, so the danger is invisible locally — yet λ-calculus
plus surjective pairing is famously not confluent (Klop 1980): with β and
fixpoints, the race to re-equalise the two copies can be made endless.  As
unoriented `when` equations, each law is one line:

```
when Unit $u : Unit ⊢ $u ≡ tt;
when σ    $p : σ    ⊢ pair (fst $p) (snd $p) ≡ $p;
```

The payoff is definitional laws on neutral terms, where rewriting is stuck.
With `rule swap $p ↪ pair (snd $p) (fst $p)`, the term `swap (swap p)`
rewrites to `pair (fst p) (snd p)` and stops — yet `swap (swap p) ≡ p`
holds, because `p`'s judgment fired the merge and both reducts share a
class.  And the graph goes strictly beyond any rule on mixed instances: if
`u ≈ v` holds only in the graph (both merge with `tt`), then
`pair (fst (k u)) (snd (k v)) ≡ k u` follows by congruence through
`k u ≈ k v`, while a rewrite could never fire — the two arguments never
become the same term.

Same anatomy as paths, one level down: the projections play path-β (oriented
computation), the `when` plays the boundary (unoriented type constraint),
and on a canonical `pair x y` the equation is already true by computation,
so only neutrals gain anything new.

## Minimal example of native and computational function extensionality

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

## The `funext` rule, e-graph action only

Typing the RHS `⟨i⟩ λx. h x · i` is routine; what matters is what it leaves
behind.  The inferred type meets the expected one:

```
  inferred:  PathP _ (λx. h x · i0) (λx. h x · i1)
  expected:  PathP _ f g
             ────────────────────────────────────── PathP injective
             G0:  λx. h x · i0 ≡ f
             G1:  λx. h x · i1 ≡ g        (stuck: no rule rewrites either side)
```

The graph closes `G0` from one leaf — the judgment `h x : PathP (B x) (f x) (g x)`:

```
  h x : PathP (B x) (f x) (g x)
  ─────────────────────────────  when (boundary)
       h x · i0  ≈  f x
  ─────────────────────────────  congruence (λ-bodies)
   λx. h x · i0  ≈  λx. f x         λx. f x  ≈  f   (η)
  ──────────────────────────────────────────────────────
              λx. h x · i0  ≈  f                          G0 ✓
```

`G1` is the same tree with `i1`/`g`.  Three moves, always in this order:
a `when` fire on a judgment, congruence to lift it through the binder,
η to meet the bare function.  The face asserts (`funext h · i0 ≡ f`)
replay the identical tree after `funext h · i0` reduces to `λx. h x · i0`.

// Minimal type-directed equalities.  Run: LP_EGRAPH=1 lambdapi check examples/eta_min.lp
//
// Rewriting decides equality by normalise-and-compare, so rules must be
// ORIENTED, SYNTAX-directed, and confluent.  The two η-laws below are
// neither: their content lives in the TYPE of a term, not in its shape.
// `when` fires them as unoriented merges into the e-graph each time the
// checker derives a judgment of the guarded type; conversion then asks for
// class equality.

// ── Unit-η: not expressible as a rule at all ────────────────────────────
// "every u : Unit is tt" has a bare variable as left-hand side: on a
// neutral u there is no syntax to match — only its type knows.
symbol Unit : TYPE; symbol tt : Unit;

when Unit $u : Unit
   ⊢ $u ≡ tt;

symbol u : Unit; symbol v : Unit;
assert ⊢ u ≡ v;                        // definitional irrelevance for Unit

// ── surjective pairing: expressible as a rule, but non-confluent ────────
symbol A : TYPE;
symbol σ : TYPE;                       // σ ≔ A × A
symbol pair : A → A → σ;
symbol fst : σ → A;
symbol snd : σ → A;
rule fst (pair $x _) ↪ $x;             // β: oriented, confluent — computation
rule snd (pair _ $y) ↪ $y;

// As a rule, [pair (fst $p) (snd $p) ↪ $p] is NON-LEFT-LINEAR: it fires only
// while its two copies of $p are SYNTACTICALLY equal, and any step inside one
// copy destroys the redex.  Its critical pairs with the projections still
// join, so local confluence holds — but β makes raw terms non-terminating,
// Newman does not apply, and global confluence actually FAILS (Klop: λβ +
// surjective pairing is not Church-Rosser; the witness needs fixpoints, so no
// finite critical-pair check can see it).  Unoriented in the graph, there is
// nothing to destroy: class membership survives any interleaving.
when σ $p : σ
   ⊢ pair (fst $p) (snd $p) ≡ $p;

symbol p : σ; symbol q : σ;
assert    ⊢ pair (fst p) (snd p) ≡ p;  // η on a NEUTRAL (the β-rules are stuck)
assertnot ⊢ p ≡ q;                     // no over-merge: distinct neutrals stay apart

// Where even the non-left-linear rule could NEVER fire: u ≈ v holds only in
// the graph (both merge with tt), never syntactically, so the two arguments
// below are forever distinct terms — congruence still closes the mixed
// instance through k u ≈ k v.
symbol k : Unit → σ;
assert ⊢ pair (fst (k u)) (snd (k v)) ≡ k u;

// The payoff: definitional involutions.  [swap (swap p)] rewrites to
// [pair (fst p) (snd p)] and is STUCK on a neutral p; η closes the loop.
symbol swap : σ → σ;
rule swap $p ↪ pair (snd $p) (fst $p);
assert ⊢ swap (swap p) ≡ p;

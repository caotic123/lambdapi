(** Evaluation and conversion. *)

open Lplib open Extra
open Common open Error open Debug
open Term
open Print

(* >> Short answer: NO graph/e-graph and NO saturation. The current engine is a
   classic Dedukti-style term rewriter — tree terms + decision-tree matching +
   a stack machine — with only a lazy-sharing optimisation that is *not* a
   congruence structure. Details:

   TERMS (Term.term, term.ml:116) are a plain inductive TREE: Vari, Type, Kind,
   Symb, Prod, Abst, Appl, LLet, Meta, Patt, Wild, Plac, TRef. Binders are HOAS
   (bind_var/unbind). The ONLY mutable/graph-ish node is
       TRef of term option Timed.ref            (term.ml:132)
   used purely for call-by-need SHARING: whnf wraps every argument with `to_tref`
   (eval.ml:195, `mk_TRef(Timed.ref(Some t))`) so a redex argument is reduced at
   most once and the result is shared in place; the `steps` counter (eval.ml:47)
   preserves physical equality. That makes a term a mutable DAG *during one
   normalisation*, but there are NO equivalence classes, NO union-find, NO
   congruence closure, and nothing is ever "saturated" — each query renormalises.

   REWRITING is decision-tree matching, not graph search: `dtree = rule
   Tree_type.dtree` (term.ml:164), one Maranget-style trie per symbol
   (`sym_dtree`, term.ml:179), consulted by the stack machine `whnf_stk cfg t stk`
   with `stack = term list` (eval.ml:212): β = `subst f u`, δ = unfold defs,
   rules = walk the dtree. Pattern vars are `Patt(i,n,ts)` (term.ml:126).

   CONVERSION (`eq_modulo`, eval.ml:125) is normalise-head-and-compare over a
   WORKLIST of pairs `(term*term) list`: unfold (δ via the config, see below) +
   whnf each side, compare heads, push child pairs. Again — syntactic comparison
   up to reduction, NOT congruence closure; no saturation, no shared e-classes.

   CONTEXT is two representations:
     • typing context `ctxt = (var * term * term option) list` (var, type,
       optional definition) — a linear assoc list; `type_of`/`def_of`
       (ctxt.ml:10,15) are `List.find`. `Ctxt.unfold` (ctxt.ml:38) rewrites a
       `Vari x` to its context definition.
     • inside eval, the config precomputes `varmap = Ctxt.to_map context :
       term VarMap.t` (eval.ml:106, ctxt.ml:61) so δ-unfolding of defined/let
       variables during conversion is a map lookup.

   RELEVANCE TO THE THESIS: the e-graph + CC(X) saturation and the ambient face
   context Φ_Γ from proposal.md/sketch.lp are exactly the machinery that does NOT
   exist here yet. Adding `theory`/`when` means layering an equivalence-class
   structure (egglog-style) and a threaded conversion-time context on top of —
   or beside — this `eq_modulo`/`whnf` pair, which today is purely
   normalise-and-compare. *)

(* >> Right — and that simplicity is the whole design bet of Dedukti/λΠ-modulo:
   the kernel stays a tiny trusted core (whnf + eq_modulo, a few hundred lines),
   and ALL the theory-specific power is pushed OUT into user rewrite rules, which
   the decision-tree compiler turns into fast matching. Untyped, orientation-based
   conversion is what keeps it this small. That's exactly why it's a good host
   for your thesis AND why the extension is delicate: every bit of cleverness you
   add (congruence/e-graph saturation, type-directed `when` guards, an ambient
   Φ_Γ) moves complexity INTO the trusted core, so each addition has to re-earn
   the three properties this simple loop currently gets for free — soundness,
   termination/decidability, and being a congruence. Keep the diff to this file
   minimal and auditable; that's the metric. *)


(* >> Careful — it's the opposite of where you'd want the analogy. Lean DOES have
   congruence closure, but NOT in its trusted kernel / definitional equality. Two
   different layers:
     • Kernel (trusted) `isDefEq`: whnf + structural compare, lazy δ-unfolding,
       η, proof irrelevance — the SAME family as lambdapi's `eq_modulo` here. No
       congruence closure, no e-graph, no saturation. Deliberately tiny/trusted.
     • Tactic/elaborator (UNtrusted): the `cc` tactic, and Lean 4's `grind`
       (CC + e-matching + theory combination, SMT-flavoured), and `simp`. These
       run congruence closure to BUILD AN EXPLICIT PROOF TERM of a *propositional*
       equality `a = b` (`Eq`), which the kernel then re-checks by ordinary defeq.
       The CC algorithm itself is never trusted — only its output proof is.
   So CC in Lean operates on PROPOSITIONAL `=` and is kernel-checked; it is not in
   conversion (`≡`). (Cf. Selsam & de Moura, "Congruence Closure in Intensional
   Type Theory", IJCAR 2016 — and note they had to use heterogeneous equality to
   even state congruence in DTT; that subtlety is exactly why CC stays at the
   proof layer there.)
   THE DISTINCTION THAT MATTERS FOR THE THESIS: your proposal puts the decision
   procedure INTO conversion — definitional, no proof term, decided by the kernel.
   That is strictly more dangerous than Lean's choice (you must keep the kernel
   sound AND conversion decidable), and it's also the novelty. The right prior art
   to compare against is therefore NOT Lean but CoqMT / Coq-Modulo-Theory (Strub;
   Blanqui–Jouannaud–Strub, "CC(X)") which genuinely embeds a theory into Coq's
   conversion — that is the line you're extending, with cubical as the stressor. *)


(* >> Yes. The discipline is: keep the trusted core change as SMALL as possible,
   and only pay for the expensive bits where a rule actually forces you to. Three
   moves, in order of how much they cost the kernel:

   1. CLASSIFY the `when`s — most don't need new machinery.
      • Orientable + type-free head (β is already a rewrite; the path BOUNDARY
        `p @ i0 ≡ u` can be a directed rule keyed on the head `papp`) → compile
        straight to the EXISTING dtree rewrite engine. ZERO core change.
      • Non-orientable / saturating (path-η, primPOr overlap-agreement) → these are
        the only ones that genuinely need an equivalence (egglog) structure.
      So "what we can reduce": push everything orientable down to rewrite rules;
      reserve the new conversion machinery for the handful that truly can't orient.
      That shrinks the dangerous surface to the overlap-agreement fragment — which
      is also the one open question (sketch.lp §7c), so nothing is wasted.

   2. THEORY = a local canonizer HOOK, not a global e-graph (yet). Register
      `theory Interval/Face` as: "when `eq_modulo` is about to compare two terms
      whose type is a registered carrier (I, F), instead of structural compare,
      canonize both via `can`/`canF` and decide with `eqDnf`." That's an extra
      branch in ONE place (the head-compare in eq_modulo), decidable per call, no
      saturation, no shared classes. Get Interval/Face De Morgan working this way
      first; defer the actual e-graph to step 3.

   3. TYPE CONSTRAINTS — this is the real fork, and it's unavoidable: today
      `eq_modulo` is UNTYPED (it takes terms, never types). A guard `when p :
      Path T u v` needs `p`'s type at conversion time. Two ways:
        (a) thread types through conversion globally → faithful to the
            unannotated surface syntax, but invasive and slows every comparison;
        (b) synthesize the type LAZILY, only when the head is a symbol that has a
            registered `when` (papp, comp, hcomp, ⌊_⌋) — infer just that subterm's
            type on demand, leave the rest untyped. Much cheaper, localized.
      Recommend (b): a `when`-trigger table (head symbol ↦ its guard), and only on
      a hit do you call `Infer` to recover `u,v`/`Φ_Γ`. Keeps the common path
      exactly as fast as now. The alternative — storing endpoints on the term at
      elaboration (CCHM `@u₀,u₁` annotation) — avoids typed conversion but throws
      away the unannotated-term win the proposal is built on, so only fall back to
      it if (b) proves too costly.

   Net: feature = "rewrite rules (free) + a carrier-typed canonizer hook in
   eq_modulo + a lazy type-on-trigger for guards", and ONLY the overlap-agreement
   case escalates to a real e-graph. Build 1→2→3, validate each against sketch.lp's
   asserts before taking the next, and keep every core edit behind the registered
   theory so plain Dedukti files pay nothing. *)


(* >> No — and this is the important correction. The e-graph is NOT inevitable for
   most of sketch.lp. Walk the mechanisms by what actually decides each case:

   • INTERVAL / FACE algebra (De Morgan, absorption, De Morgan duality, …) is a
     CANONIZER, i.e. Shostak-style with `solve ≔ none` — `can`/`canF` compute a
     normal form (Dnf) and `eqDnf` compares it. A canonizer is a NORMAL-FORM
     FUNCTION, not an e-graph. Decidable by a function call. No saturation.

   • CONGRUENCE over the uninterpreted cubical operators (`p @ ((i∨j)∧i) ≡ p @ i`,
     sketch.lp:141) you get FOR FREE from the existing `eq_modulo`: it already
     recurses `p @ a` vs `p @ b` into `a` vs `b`, and the canonizer hook decides
     `a ≡ b`. Structural-recursion-of-conversion IS congruence closure for the
     DIRECTED case. Still no e-graph.

   • PATH-η (`pabs (λi, p@i) ≡ p`) is just η — handle it the way Lean/Agda handle
     function/record η: TYPE-DIRECTED η-expansion on demand inside eq_modulo (when
     one side is `pabs`-headed at Path type, η-expand the other). Needs the typed-
     conversion hook from step 3, NOT saturation.

   • BOUNDARY / β and the primPOr RESTRICTIONS (i) are orientable → ordinary
     guarded rewrite rules. No e-graph.

   What's LEFT pulling toward egglog is exactly ONE thing: the overlap-agreement
   coherence (ii) under primPOr — non-orientable (`⌊u⌋ ≡ ⌊v⌋`, no canonical side),
   mutually triggering, and worst under metavariables (proposal §3). And even THAT
   has a non-e-graph route: discharge it as an ELABORATION-TIME coherence
   obligation (a finite conversion check when primPOr is formed, à la Cubical
   Agda's CtSplitPartial), rather than a conversion-time saturating rule. As
   sketch.lp:210 notes, (ii) is derivable from (i) by transitivity, so on closed
   terms reducing through (i) already decides it.

   So the honest picture: you can build and pass ALMOST ALL of sketch.lp with
   {canonizer hook + structural congruence + typed η + orientable rewrites} and
   NO e-graph. The e-graph is the tool of LAST RESORT for one case — saturating
   overlap-agreement during conversion when terms carry metavariables and merges
   enable merges in an order structural recursion can't discover. Whether that
   case truly forces an e-graph (vs. an elaboration-time check) IS the thesis's
   open question — so "inevitable" is precisely what's unproven, not a given.
   Practical consequence: don't build the e-graph first. Build 1+2+typed-η, get
   §1–§6 of sketch.lp green, and only then attack §7c — at which point you'll know
   empirically whether you can avoid egglog or not. *)

(* >> Checked the actual Agda source (src/full/Agda/TypeChecking/Primitive/
   Cubical*.hs, github.com/agda/agda). Short version: Agda does NOT propagate
   constraints via any e-graph / congruence closure — it uses a DNF CANONIZER
   plus substitution-forcing, i.e. exactly the design sketch.lp already encodes.

   INTERVAL / DE MORGAN. The interval is reduced by a normal form. The core fn is
       decomposeInterval :: Term -> ReduceM [[(Int, Bool)]]
   i.e. an interval expression → a list of conjunctive clauses, each clause a list
   of (variable, polarity) literals = DISJUNCTIVE NORMAL FORM (join of meets of
   signed literals). `primIMin` (∧), `primIMax` (∨), `primINeg` (~) are reduced
   through `intervalView` pattern-matching with IZero/IOne terminal cases. THAT IS
   LITERALLY sketch.lp's `Dnf` / `can` / `conjD`/`disjD`/`negD`: a list-of-signed-
   literal-sets canonizer, equality by normal-form compare (`eqDnf`). So `theory
   Interval` isn't speculative — it's a re-encoding of what Agda already does, as
   a registered canonizer instead of hard-wired primitive reductions. De Morgan
   laws (~~i=i, distributivity, absorption) fall out of the normal form, no
   propagation.

   FACES / SYSTEMS. A face/cofibration (IsOne φ) is decided the same way — DNF on
   the face lattice; `combineSys` / `decomposeInterval` split a system by its
   faces. "Propagation" here is just SUBSTITUTION-forcing: to work on the i=0
   face, substitute i:=i0 and renormalise; face entailment φ⊨ψ is a normal-form
   query, not a fixpoint. No union-find, no saturation.

   SYSTEM OVERLAP COHERENCE (the primPOr "agree on the intersection" condition) is
   checked when the SYSTEM IS FORMED — the partial-element/`compData`/
   `transpSysTel'` machinery requires the branches to agree on overlapping faces,
   via face-restricted conversion at elaboration time. NOT a conversion-time
   saturating rule. This is direct external validation of the recommendation two
   comments up: overlap-agreement as an ELABORATION obligation (their
   CtSplitPartial), not an e-graph.

   BOTTOM LINE for the thesis: Agda's whole §1–§6 equivalent runs on {DNF
   canonizer + substitution forcing + elaboration-time system coherence} — no
   e-graph anywhere. So you can mirror them exactly for the bulk, and the e-graph
   stays reserved for the one thing Agda does NOT do in conversion: saturate
   overlap-agreement under METAVARIABLES (Agda sidesteps it by only checking
   coherence on concrete, fully-given systems). That gap is precisely your novelty
   — and confirms it's narrow.
   Refs: github.com/agda/agda src/full/Agda/TypeChecking/Primitive/Cubical/ ;
   Vezzosi–Mörtberg–Abel, "Cubical Agda" (ICFP 2019),
   staff.math.su.se/anders.mortberg/papers/cubicalagda.pdf *)

(* >> Added to sketch.lp (in §5, right after the "interval theory fires UNDER
   paths" assert). It defines:
       symbol f g : A → A;
       symbol hpt : Π (x:A), Path A (f x) (g x);          // pointwise path
       symbol funext : (Π x, Path A (f x) (g x)) → Path (A→A) f g;
       rule funext $h ↪ pabs (A→A) (λ i, λ x, ($h x) @ i);
   plus three asserts:
     • ((funext hpt) @ i) t ≡ hpt t @ i      — pointwise computation, pure β;
     • (funext hpt) @ i0 ≡ f  and  @ i1 ≡ g  — the two boundaries.
   The point of choosing funext: it is the cleanest case where the boundary
   `when` must fire UNDER a binder — `hpt x : Path A (f x) (g x)` is only known by
   reading the type of `hpt x` beneath `λ x`, then η closes `λ x, f x ≡ f`. So it
   doubles as the minimal motivating example for the TYPE-DIRECTED conversion of
   step 3 (eval comment above / proposal.md §"Metatheory" 3): an untyped engine
   literally cannot discharge `(funext hpt) @ i0 ≡ f`. Note it parses but does NOT
   check in stock lambdapi (needs `when`/`theory`) — it's an illustrative target,
   same status as the rest of sketch.lp. *)

(* >> Your instinct is right, and it has a precise name — but it splits in two and
   only ONE half is unification. Let me separate them, because the split is the
   whole design.

   WHAT YOU'RE DESCRIBING. "Don't substitute i:=i0 and reduce; instead ADD the
   equation `p x i0 = f x` to a context Θ′ and decide conversion *modulo* Θ′."
   That is exactly CONVERSION MODULO A SET OF GROUND EQUATIONS, and Θ′ is — quite
   literally — an e-graph: "add equation a = b" == "union the classes of a and b";
   "decide ≡ under Θ′" == "are they in the same class after congruence closure".
   So you haven't avoided the e-graph by introducing Θ′; you've REDISCOVERED it.
   Θ′ IS the e-graph, and the proposal's Φ_Γ is the cofibration slice of it.

   IS IT UNIFICATION? Only in the metavariable case — and that distinction is the
   one to write down:
     • GROUND (f, g, p closed; your sketch.lp funext): adding `p x i0 = f x` and
       closing under congruence is GROUND CONGRUENCE CLOSURE — decidable, total,
       and ORDER-INDEPENDENT. The order-worry you raise ("the order may affect
       it") is exactly what saturation-to-a-fixpoint removes: the congruence
       closure of a set of equations is unique regardless of merge order (the
       egglog/Kleene-fixpoint guarantee). So if you saturate, order can't bite.
       It only bites if you do ad-hoc DIRECTED rewriting with Θ′ — which is the
       very non-confluence you're trying to escape. Saturation is the cure, not
       a new disease.
     • WITH METAVARS (`?K : PathP (λi.?B i) f g`, `?p`): now "add `?p @ i0 = f`"
       can force a solution of `?B`/`?p`, so deciding the equation INTERLEAVES
       with solving metavariables = E-UNIFICATION (unification modulo the path/
       face theory). THIS is the hard, possibly-non-terminating half — proposal
       §"Metatheory" 3, and sketch.lp §7c's "saturation interleaves with
       unification." Ground Θ′ is decidable; metavar Θ′ is the open question.

   WHY YOUR "ADD, DON'T REDUCE" CHOICE IS CORRECT (and why it implies the e-graph).
   Boundary-as-oriented-rewrite (`p x i0 ↪ f x`) is fragile precisely because path
   types create critical pairs it can't confluently resolve — your own worry.
   Refusing to orient, and instead UNIONING `p x i0` with `f x` and congruence-
   closing, is the standard escape (Nelson–Oppen / egglog): equivalence, not
   orientation. So "always add more information" is the right instinct — but it
   buys you the e-graph's obligations, not freedom from them:
     – SOUNDNESS: every equation you add to Θ′ must be a REAL definitional
       equality, else you collapse the theory (this is what `consistent ≔ wf`
       guards — reject Θ′ that forces i0 = i1). "Add more info" is only safe up to
       consistency.
     – TERMINATION: ground closure terminates; the metavar case is the thing the
       thesis must bound. Don't promise it, prove it (or bound the e-matching
       depth).

   YOUR RULE SKETCH, cleaned up. What you wrote as
       when ?K : PathP (λ i → ?B i) f g,  ?p : Path ?K i0  --->  ?p i0 [= f]
   is the metavariable-generalised §3 boundary `when`: for `?p : PathP ?B f g`,
   register `?p @ i0 = f` (and `?p @ i1 = g`) into Θ′. Two corrections:
     (1) `Path ?K i0` is ill-formed — you mean the application `?p @ i0`, not a
         Path-type; the endpoints f,g come from ?p's TYPE `PathP ?B f g`, read by
         the guard (the unannotated win).
     (2) the head must be `?p @ i0`, not `?K`. So: `when ?p : PathP ?B f g ⊢
         ?p @ i0 ≡ f ⊢ ?p @ i1 ≡ g`, with the understanding that ⊢ here MERGES
         into Θ′ rather than orienting.
   You're right it's undocumented — it should be the central judgement of the
   proposal: write conversion as `Θ′ ⊢ a ≡ b`, state that boundary/η/overlap
   `when`s ACT BY MERGING into Θ′, prove ground decidability, and isolate the
   metavar/E-unification case as the open problem. Implementation order follows:
   ground e-graph first (funext, §1–§6), metavar interleaving last (§7c). *)


(* >> Yes — and that is very likely the right design for the KERNEL. Better: the
   funext example you just added is ALREADY ground. `f`, `g`, `hpt` are declared
   `symbol`s, not metavariables; so `(funext hpt) @ i0 ≡ f` is a ground conversion,
   decided by ground congruence closure over Θ′. Nothing in §1–§6 of sketch.lp,
   the squares (§7b), or funext needs a metavariable. They're all ground.

   WHERE METAVARS ACTUALLY COME FROM: not the mathematics — ELABORATION. They're
   inserted for implicit/inferred arguments of the UNANNOTATED surface syntax
   (write `funext h` and the elaborator invents `?A ?B ?f ?g` and solves them).
   The CORE cubical calculus (CCHM/CHM) has NO metavariables; its canonicity /
   normalisation metatheory is stated for GROUND terms. So "do it with only ground
   variables" isn't a restriction of the math — it's literally the formal system
   the soundness/decidability proofs are about. Metavar E-unification is an
   elaboration-UX layer bolted on top, not part of the object of study.

   THE DESIGN THAT FALLS OUT (and it's the Lean discipline again):
     • KERNEL / conversion: ground only. Θ′ accumulates ground equations,
       congruence-close to a fixpoint — finite, order-independent, DECIDABLE. This
       carries all of §1–§6 + the squares. The open question (saturation under
       metavars) simply does not arise here.
     • ELABORATOR (untrusted): solve metavariables by ORDINARY pattern (Miller)
       unification — NOT modulo the path/face theory. When a metavar can only be
       pinned by a theory equation (the genuinely E-unification case), DON'T solve
       it in the theory: postpone, or require the user to annotate. Then hand a
       fully ground term to the kernel.
   Net: you confine everything decidable to the trusted core and keep the one
   undecidable-in-general thing (theory E-unification) out of it entirely.

   THE PRICE — and it's exactly the proposal's central tension. A ground-only
   kernel means some terms Agda elaborates via theory-aware unification will, here,
   need the user to WRITE the endpoints/faces — i.e. you partly give back the
   `@u₀,u₁` annotation that proposal line 4 set out to eliminate. So "unannotated
   surface syntax" and "ground-only decidable kernel" pull against each other:
     – ground kernel + best-effort syntactic elaboration  = shippable, decidable,
       matches the metatheory, occasionally asks for an annotation;
     – theory E-unification in elaboration  = fewer annotations, but reopens the
       termination question.
   Recommendation: BUILD the ground kernel (it's the thesis's provable core and it
   already covers funext/the squares), and treat theory-aware elaboration as a
   clearly-scoped extension whose termination is the stated open problem. You lose
   nothing provable by staying ground; you only trade some inference convenience —
   and you can measure exactly how often, by counting the annotations sketch.lp
   would need under a ground-only elaborator. *)

(* >> The fix is a change of KIND of variable, and it dissolves the whole worry.
   Your `?K, ?p, ?B` are written as METAVARIABLES — unknowns to be SOLVED by
   unification. But a `when`/rewrite rule never solves anything: its variables are
   PATTERN (schema) variables, bound by MATCHING against whatever ground term
   shows up. In lambdapi surface they're the `$`-vars. So you don't write the rule
   over metavariables at all — you write ONE schema:

       when $p : Path $T $u $v  ⊢  $p @ i0 ≡ $u  ⊢  $p @ i1 ≡ $v

   ($p,$T,$u,$v are slots, not unknowns.) "Representing it with ground variables"
   is exactly what happens when this schema FIRES: it matches a CONCRETE subject
   and every slot is instantiated to a GROUND subterm. Concretely, on your funext:

     subject     = funext hpt                       -- ground; hpt is a symbol
     its type     = Path (A→A) f g                   -- ground f, g
     match        ⟹ $p := funext hpt, $T := A→A, $u := f, $v := g   (all ground)
     fires        ⟹ MERGE into Θ′:  (funext hpt) @ i0 = f
                                      (funext hpt) @ i1 = g          -- ground eqns
     Θ′ ground    ⟹ congruence closure decides ≡.   No `?` ever exists.

   So the metavariable-laden rule you wrote and the ground story are the SAME rule;
   the `?`s were never needed. The schema is parametric; GROUNDNESS is a property
   of the SUBJECT, not of the rule. Two regimes:

     • SUBJECT GROUND (funext hpt, the squares, all of §1–§6): matching binds slots
       to ground terms → ground equations into Θ′ → decidable. This is "the same
       thing using ground variables" — you already have it.
     • SUBJECT CONTAINS A METAVARIABLE (you wrote `funext ?h`, so its type is
       `Path (A→A) ?f ?g`): now firing tries to merge `(funext ?h) @ i0 = ?f`,
       which can SOLVE ?f — that's the E-unification case. It is triggered by the
       SUBJECT carrying `?`, never by the rule.

   Practical rule of thumb, then: keep every `when` a `$`-pattern schema (never
   `?`), and guarantee the subject handed to conversion is ground (elaborate /
   solve metavars first, per the previous comment). Under that discipline your
   `?K…?p` rule is literally the `$p`-schema above, and the hard case simply never
   reaches the kernel. Correction to the term you wrote, for the record: `Path ?K
   i0` is still ill-formed — the endpoint obligation is the APPLICATION `$p @ i0`,
   with `$u`(=f) read from `$p`'s type; there is no `Path … i0` type. *)


(* >> Done. Updated both docs to the settled design — with one precision kept so
   the claim stays defensible: the e-graph IS inevitable and embraced as the core
   mechanism (merge into Θ′, don't orient — stop fighting confluence), BUT that's
   the GROUND e-graph, which is decidable. The only thing still open is the
   metavariable/E-unification case. I kept those two apart rather than saying
   "e-graph saturation is the open question" flat, because the ground e-graph is
   exactly what makes funext/the squares/§1–§6 decidable — it's the solution, not
   the problem.
   Edits:
     • proposal.md — new section "Design conclusion: one judgement, Θ′ ⊢ a ≡ b —
       merge, don't orient": states conversion as Θ′ ⊢ a ≡ b with Θ′ an e-graph,
       `when` MERGES (no orientation), the confluence argument (order-independent
       closure), the ground/metavariable split, and the ground-only kernel +
       elaborator discipline. Also sharpened the "three walls → one question" line
       to name the ground (decided) vs metavariable (open) split, and noted the
       funext demo.
     • sketch.lp — a "DESIGN (settled)" header block right after the require:
       Θ′ ⊢ a ≡ b, theory=canonizer / when=merge, why merge-not-orient, and the
       ground-decidable vs metavar-open split, cross-referencing proposal.md.
   Net effect: the framework's pitch is now "one judgement + an e-graph you stop
   fighting confluence with", and the scary surface is reduced to a single, named,
   scoped open case. *)

(* >> Two answers.
   DO WE STILL NEED `theory`? Not redundant, but SEPARABLE — and not needed for
   the core. It is the "X" of CC(X): an efficient CANONIZER (Dnf) that decides the
   interval/face De Morgan algebra in one normal-form call. The e-graph alone is a
   BAD substitute for that algebra — pushing commutativity / distributivity /
   absorption in as merge rules makes the e-graph blow up (AC saturation), exactly
   the wall the canonizer exists to avoid. So once you want the De Morgan
   assert/assertnot battery (i∧j ≡ j∧i, distributivity, no-excluded-middle),
   `theory` earns its place. BUT the path core — boundary, β, η, funext — never
   touches ∧/∨/~; it needs only i0,i1. So `theory` is cleanly droppable for a
   first version. Keep CC(X) factored: e-graph = CC (congruence over the cubical
   formers), canonizer = X (the interval algebra); ship CC first, add X later.

   CREATED sketch_simple.lp — the minimal core, no `theory`, no faces:
     • interval = just {i0, i1} (no ∧/∨/~, no Dnf, no canonizer);
     • Path/pabs/papp, β as an ordinary rewrite;
     • boundary + path-η as `when`s that MERGE into Θ′;
     • ground demonstrations: the three path asserts + the funext block.
   Everything there is ground, so it is decided by ground congruence closure
   alone — it exercises THE settled mechanism (Θ′ ⊢ a ≡ b, merge-not-orient) with
   nothing else in the way. That makes it the right first implementation target:
   get sketch_simple green, then layer `theory Interval/Face` back in for the
   algebra (sketch.lp), then the metavariable case last. *)

(* >> Checked. Three real OCaml options, and they sort by purpose:

   • ego  (verse-lab/ego, on opam, v0.0.6) — e-graphs in OCaml, modelled on Rust's
     `egg`: equality saturation, generic over user analyses, with cost-based
     extraction. THE direct match for the Θ′ / merge-not-orient mechanism. Its
     Ego.Generic interface (custom analysis + merge hook) can host the canonizer
     as an analysis and `wf` as a merge guard. Best for PROTOTYPING the ground
     e-graph fast. Caveat: 0.0.x, research-grade — verify activity, and it's a
     dependency you'd be putting near the kernel.
   • sidekick  (c-cube/sidekick, Simon Cruanes) — modular CDCL(T) SMT framework
     whose core IS a congruence closure with theory combination and [wip] proof
     generation. Architecturally the closest to CC(X) AND to the proposal's
     "Alethe-style certificate per merge" line. Heavier and SMT-solver-shaped, but
     the right reference if you want certificates + theory combination later. Its
     `Sidekick_cc` is the component to look at.
   • Alt-Ergo's CC(X)  (Conchon–Contejean) — the literal architecture proposal §3
     cites. Not a standalone lib (embedded in Alt-Ergo), so it's the PAPER/CODE
     reference, not a dependency.

   RECOMMENDATION: prototype with `ego` (fastest to a working saturation experiment
   in the language you know from egglog); keep `sidekick` as the model for the
   eventual CC(X)+certificate kernel; cite Alt-Ergo CC(X) as the design ancestor.

   BUT the gating caveat, independent of which lib: classical congruence closure /
   e-graphs are FIRST-ORDER — uninterpreted functions over ground terms. Lambdapi
   terms have BINDERS (λ, Π) and the cubical formers apply to functions (funext
   merges UNDER λ x). Neither ego nor sidekick-cc handles HOAS/α-equivalence
   natively. So whichever you pick, you must decide how binders enter the e-graph:
   treat closed sub-λ's as opaque leaves (hash-consed up to α), or de-Bruijn-encode,
   or e-graph only the first-order skeleton and recurse structurally under binders.
   That decision — not the library choice — is the real work.

   And a TCB note consistent with "minimal, auditable" (eval.ml:60): a 0.0.x
   dependency inside the TRUSTED core enlarges the soundness surface. Fine for the
   experiment; for the shipped kernel, a SMALL bespoke ground congruence closure
   (union-find + signature table, a few hundred lines) may be the auditable choice,
   with ego/sidekick as the oracle you validate it against.
   Refs: github.com/verse-lab/ego (opam: `ego`) ; github.com/c-cube/sidekick ;
   Conchon–Contejean CC(X) (Alt-Ergo). *)

 (** The head-structure of a term t is:
- λx:_,h if t=λx:a,u and h is the head-structure of u
- Π if t=Πx:a,u
- h _ if t=uv and h is the head-structure of u
- ? if t=?M[t1,..,tn] (and ?M is not instantiated)
- t itself otherwise (TYPE, KIND, x, f)

A term t is in head-normal form (hnf) if its head-structure is invariant by
reduction.

A term t is in weak head-normal form (whnf) if it is an abstration or if it
is in hnf. In particular, a term in head-normal form is in weak head-normal
form.

A term t is in strong normal form (snf) if it cannot be reduced further.
*)

(** Logging function for whnf. *)
let log_whnf = Logger.make 'w' "whnf" "whnf"
let log_whnf = log_whnf.pp

(** Logging function for snf. *)
let log_snf = Logger.make 'e' "snf " "snf"
let log_snf = log_snf.pp

(** Logging function for conversion. *)
let log_conv = Logger.make 'c' "conv" "conversion"
let log_conv = log_conv.pp

(** Logging function for rewriting. *)
let log_rew = Logger.make 'q' "rewr" "rewriting"
let log_rew = log_rew.pp

(** Convert modulo eta. *)
let eta_equality : bool Timed.ref = Console.register_flag "eta_equality" false

(** Counter used to preserve physical equality in {!val:whnf}. *)
let steps : int Stdlib.ref = Stdlib.ref 0

(** {1 Define reduction functions parametrised by {!whnf}} *)

(** [hnf whnf t] computes a hnf of [t] using [whnf]. *)
let hnf : (term -> term) -> (term -> term) = fun whnf ->
  let rec hnf t =
    match whnf t with
    | Abst(a,t) -> mk_Abst(a, let x,t = unbind t in bind_var x (hnf t))
    | t -> t
  in hnf

(** [snf whnf t] computes a snf of [t] using [whnf]. *)
let snf : (term -> term) -> (term -> term) = fun whnf ->
  let rec snf t =
    if Logger.log_enabled() then log_snf "snf %a" term t;
    let t = whnf t in
    if Logger.log_enabled() then log_snf "whnf = %a" term t;
    match t with
    | Vari _
    | Type
    | Kind
    | Symb _
    | Plac _ (* may happen when reducing coercions *)
      -> t
    | LLet(_,t,b) -> snf (subst b t)
    | Prod(a,b) ->
      mk_Prod(snf a, let x,b = unbind b in bind_var x (snf b))
    | Abst(a,b) ->
      mk_Abst(snf a, let x,b = unbind b in bind_var x (snf b))
    | Appl(t,u) -> mk_Appl(snf t, snf u)
    | Meta(m,ts) -> mk_Meta(m, Array.map snf ts)
    | Patt(i,n,ts) -> mk_Patt(i,n,Array.map snf ts)
    | Bvar _ -> assert false
    | Wild -> assert false
    | TRef _ -> assert false
  in snf

type rw_tag = [ `NoBeta | `NoRw | `NoExpand ]

(** Configuration of the reduction engine. *)
module Config = struct

  type t =
    { varmap : term VarMap.t (** Variable definitions. *)
    ; rewrite : bool (** Whether to apply user-defined rewriting rules. *)
    ; expand_defs : bool (** Whether to expand definitions. *)
    ; beta : bool (** Whether to beta-normalise *)
    ; dtree : sym -> dtree (** Retrieves the dtree of a symbol *) }

  (** [make ?dtree ?rewrite c] creates a new configuration with
      tags [?rewrite] (being empty if not provided), context [c] and
      dtree map [?dtree] (defaulting to getting the dtree from the symbol).
      By default, beta reduction and rewriting is enabled for all symbols. *)
  let make : ?dtree:(sym -> dtree) -> ?tags:rw_tag list -> ctxt -> t =
  fun ?(dtree=fun sym -> Timed.(!(sym.sym_dtree))) ?(tags=[]) context ->
    let beta = not @@ List.mem `NoBeta tags in
    let expand_defs = not @@ List.mem `NoExpand tags in
    let rewrite = not @@ List.mem `NoRw tags in
    {varmap = Ctxt.to_map context; rewrite; expand_defs; beta; dtree}

  (** [unfold cfg a] unfolds [a] if it's a variable defined in the
      configuration [cfg]. *)
  let rec unfold : t -> term -> term = fun cfg a ->
    match Term.unfold a with
    | Vari x as a ->
      begin match VarMap.find_opt x cfg.varmap with
        | None -> a
        | Some v -> unfold cfg v
      end
    | a -> a

end

type config = Config.t

(** [eq_modulo whnf a b] tests the convertibility of [a] and [b] using
    [whnf]. *)
let eq_modulo : (config -> term -> term) -> config -> term -> term -> bool =
  fun whnf ->
  let rec eq : config -> (term * term) list -> unit = fun cfg l ->
    match l with
    | [] -> ()
    | (a,b)::l ->
    if Logger.log_enabled () then log_conv "eq: %a ≡ %a" term a term b;
    if LibTerm.eq_alpha a b then eq cfg l else
    let a = Config.unfold cfg a and b = Config.unfold cfg b in
    match a, b with
    | LLet(_,t,u), _ ->
      let x,u = unbind u in
      eq {cfg with varmap = VarMap.add x t cfg.varmap} ((u,b)::l)
    | _, LLet(_,t,u) ->
      let x,u = unbind u in
      eq {cfg with varmap = VarMap.add x t cfg.varmap} ((a,u)::l)
    | Patt(None,_,_), _ | _, Patt(None,_,_) -> assert false
    | Patt(Some i,_,ts), Patt(Some j,_,us) ->
      if i=j then eq cfg (List.add_array2 ts us l) else raise Exit
    | Kind, Kind
    | Type, Type -> eq cfg l
    | Vari x, Vari y -> if eq_vars x y then eq cfg l else raise Exit
    | Symb f, Symb g when f == g -> eq cfg l
    | Prod(a1,b1), Prod(a2,b2)
    | Abst(a1,b1), Abst(a2,b2) ->
      let _,b1,b2 = unbind2 b1 b2 in eq cfg ((a1,a2)::(b1,b2)::l)
    | Abst _, (Type|Kind|Prod _)
    | (Type|Kind|Prod _), Abst _ -> raise Exit
    | (Abst(_ ,b), t | t, Abst(_ ,b)) when Timed.(!eta_equality) ->
      let x,b = unbind b in eq cfg ((b, mk_Appl(t, mk_Vari x))::l)
    | Meta(m1,a1), Meta(m2,a2) when m1 == m2 ->
      eq cfg (if a1 == a2 then l else List.add_array2 a1 a2 l)
    (* cases of failure *)
    | Kind, _ | _, Kind
    | Type, _ | _, Type -> raise Exit
    | ((Symb f, (Vari _|Meta _|Prod _|Abst _))
      | ((Vari _|Meta _|Prod _|Abst _), Symb f)) when is_constant f ->
      raise Exit
    | _ ->
    let a = whnf cfg a and b = whnf cfg b in
    if Logger.log_enabled () then log_conv "whnf: %a ≡ %a" term a term b;
    match a, b with
    | Patt(None,_,_), _ | _, Patt(None,_,_) -> assert false
    | Patt(Some i,_,ts), Patt(Some j,_,us) ->
      if i=j then eq cfg (List.add_array2 ts us l) else raise Exit
    | Kind, Kind
    | Type, Type -> eq cfg l
    | Vari x, Vari y when eq_vars x y -> eq cfg l
    | Symb f, Symb g when f == g -> eq cfg l
    | Prod(a1,b1), Prod(a2,b2)
    | Abst(a1,b1), Abst(a2,b2) ->
      let _,b1,b2 = unbind2 b1 b2 in eq cfg ((a1,a2)::(b1,b2)::l)
    | (Abst(_ ,b), t | t, Abst(_ ,b)) when Timed.(!eta_equality) ->
      let x,b = unbind b in eq cfg ((b, mk_Appl(t, mk_Vari x))::l)
    | Meta(m1,a1), Meta(m2,a2) when m1 == m2 ->
      eq cfg (if a1 == a2 then l else List.add_array2 a1 a2 l)
    | Appl(t1,u1), Appl(t2,u2) -> eq cfg ((u1,u2)::(t1,t2)::l)
    | Bvar _, _ | _, Bvar _ -> assert false
    | _ -> raise Exit
  in
  fun cfg a b ->
  if Logger.log_enabled () then log_conv "eq_modulo: %a ≡ %a" term a term b;
  try eq cfg [(a,b)]; true
  with Exit -> if Logger.log_enabled () then log_conv "failed"; false

(** Abstract machine stack. *)
type stack = term list

(** [to_tref t] transforms {!constructor:Appl} into
   {!constructor:TRef}. *)
let to_tref : term -> term = fun t ->
  match t with
  | Appl _ -> mk_TRef(Timed.ref(Some t))
  | Symb s when s.sym_prop <> Const -> mk_TRef(Timed.ref(Some t))
  | t -> t

(** {1 Define the main {!whnf} function that takes a {!config} as argument} *)
let depth = Stdlib.ref 0

(** [whnf cfg t] computes a whnf of the term [t] wrt configuration [c]. *)
let rec whnf : config -> term -> term = fun cfg t ->
  let n = Stdlib.(!steps) in
  let u, stk = whnf_stk cfg t [] in
  if Stdlib.(!steps) <> n then add_args u stk else unfold t

(** [whnf_stk cfg t stk] computes a whnf of [add_args t stk] wrt
    configuration [c]. *)
and whnf_stk : config -> term -> stack -> term * stack = fun cfg t stk ->
  if Logger.log_enabled () then
    log_whnf "%awhnf_stk %a %a" D.depth !depth term t (D.list term) stk;
  let t = unfold t in
  match t, stk with
  | Appl(f,u), stk -> whnf_stk cfg f (to_tref u::stk)
  (*| _ ->
  if Logger.log_enabled () then
    log_whnf "%awhnf_stk %a%a %a" D.depth !depth term t (D.list term) stk;
  match t, stk with*)
  | Abst(_,f), u::stk when cfg.Config.beta ->
    Stdlib.incr steps; whnf_stk cfg (subst f u) stk
  | LLet(_,t,u), stk ->
    Stdlib.incr steps; whnf_stk cfg (subst u t) stk
  | (Symb s as h, stk) as r ->
    begin match Timed.(!(s.sym_def)) with
      (* The invariant that defined symbols are subject to no
         rewriting rules is false during indexing for websearch;
         that's the reason for the when in the next line *)
    | Some t when Tree_type.is_empty (cfg.dtree s) ->
      if Timed.(!(s.sym_opaq)) || not cfg.Config.expand_defs then r
      else (Stdlib.incr steps; whnf_stk cfg t stk)
    | None when not cfg.Config.rewrite -> r
    | _ ->
      (* If [s] is modulo C or AC, we put its arguments in whnf and reorder
         them to have a term in AC-canonical form. *)
      let stk =
        if is_modulo s then
          let n = Stdlib.(!steps) in
          (* We put the arguments in whnf. *)
          let stk' = List.map (whnf cfg) stk in
          if Stdlib.(!steps) = n then (* No argument has been reduced. *)
            stk
          else (* At least one argument has been reduced. *)
            (* We put the term in AC-canonical form. *)
            snd (get_args (add_args h stk'))
        else stk
      in
      let n = Stdlib.(!steps) in
      match tree_walk cfg s stk with
      | None -> Stdlib.(steps := n); h, stk
      | Some (t', stk') ->
        if Logger.log_enabled () then
          log_whnf "%aapply rewrite rule" D.depth !depth;
        Stdlib.incr steps; whnf_stk cfg t' stk'
    end
  | (Vari x, stk) as r ->
    begin match VarMap.find_opt x cfg.varmap with
    | Some v -> Stdlib.incr steps; whnf_stk cfg v stk
    | None -> r
    end
  | r -> r

(** {b NOTE} that in {!val:tree_walk} matching with trees involves two
    collections of terms.
    1. The argument stack [stk] of type {!type:stack} which contains the terms
       that are matched against the decision tree.
    2. An array [vars] containing subterms of the argument stack [stk] that
       are filtered by a pattern variable. These terms may be used for
       non-linearity or free-variable checks, or may be bound in the RHS.

    The [bound] array is similar to the [vars] array except that it is used to
    save terms with free variables. *)

(** {b NOTE} in the {!val:tree_walk} function, bound variables involve three
    elements:
    1. a {!constructor:Term.term.Abst} which introduces the bound variable in
       the term;
    2. a {!constructor:Term.term.Vari} which is the bound variable previously
       introduced;
    3. a {!constructor:Tree_type.TC.t.Vari} which is a simplified
       representation of a variable for trees. *)

(** [tree_walk cfg s stk] tries to apply a rewrite rule by matching the stack
    [stk] against the decision tree of [s]. The resulting state of the
    abstract machine is returned in case of success. Even if matching fails,
    the stack [stk] may be imperatively updated since a reduction step taken
    in elements of the stack is preserved (this is done using
    {!constructor:Term.term.TRef}). *)
and tree_walk : config -> sym -> stack -> (term * stack) option =
  fun cfg s stk ->
  let (lazy capacity, lazy tree) = cfg.dtree s in
  let vars = Array.make capacity mk_Kind in (* dummy terms *)
  let bound = Array.make capacity None in
  (* [walk tree stk cursor vars_id id_vars] where [stk] is the stack of terms
     to match and [cursor] the cursor indicating where to write in the [vars]
     array described in {!module:Term} as the environment of the RHS during
     matching. [vars_id] maps the free variables contained in the term to the
     indexes defined during tree build, and [id_vars] is the inverse mapping
     of [vars_id]. *)
  let rec walk tree stk cursor vars_id id_vars =
    if Logger.log_enabled() then
      log_rew "%awalk %a %a %d %a" D.depth !depth
        sym s (D.list term) stk cursor
        (D.map VarMap.iter Raw.var "," D.int ";") vars_id;
    let open Tree_type in
    match tree with
    | Fail -> None
    | Leaf(rhs_subst, r) -> (* Apply the RHS substitution *)
        (* Allocate an environment where to place terms coming from the
           pattern variables for the action. *)
        assert (List.length rhs_subst = r.vars_nb);
        let env_len = r.vars_nb + r.xvars_nb in
        let env = Array.make env_len None in
        (* Retrieve terms needed in the action from the [vars] array. *)
        let f (pos, (slot, xs)) =
          match bound.(pos) with
          | Some(_) -> env.(slot) <- bound.(pos)
          | None    ->
              let var id = try IntMap.find id id_vars
                           with Not_found -> assert false in
              let xs = Array.map var xs in
              env.(slot) <- Some(bind_mvar xs vars.(pos))
        in
        List.iter f rhs_subst;
        (* Complete the array with fresh meta-variables if needed. *)
        for i = r.vars_nb to env_len - 1 do
          env.(i) <- Some(bind_mvar [||] (mk_Plac false))
        done;
        Some (subst_patt env r.rhs, stk)
    | Cond({ok; cond; fail})                              ->
        let next =
          match cond with
          | CondNL((i,vi), (j,vj)) ->
              if Logger.log_enabled() then
                log_rew "%aCondNL(%d[%a],%d[%a]) %a ≟ %a" D.depth !depth
                  i (Array.pp D.int ",") vi j (Array.pp D.int ",") vj
                  Raw.term vars.(i) Raw.term vars.(j);
              let var id = try IntMap.find id id_vars
                           with Not_found -> assert false in
              let vj = Array.map var vj in
              let bj = bind_mvar vj vars.(j) in
              let vi = Array.map (fun id -> mk_Vari (var id)) vi in
              let tj = msubst bj vi in
              if eq_modulo whnf cfg vars.(i) tj then ok else fail
          | CondFV(i,xs) ->
              let allowed =
                (* Variables that are allowed in the term. *)
                let fn id =
                  try IntMap.find id id_vars with Not_found -> assert false
                in
                Array.map fn xs
              in
              let forbidden =
                (* Term variables forbidden in the term. *)
                IntMap.filter (fun id _ -> not (Array.mem id xs)) id_vars
              in
              (* Ensure there are no variables from [forbidden] in [b]. *)
              let no_forbidden b =
                not (IntMap.exists (fun _ x -> occur_mbinder x b)
                       forbidden)
              in
              (* We first attempt to match [vars.(i)] directly. *)
              let b = bind_mvar allowed vars.(i) in
              if no_forbidden b
              then (bound.(i) <- Some b; ok) else
              (* As a last resort we try matching the SNF. *)
              let b = bind_mvar allowed (snf (whnf cfg) vars.(i)) in
              if no_forbidden b
              then (bound.(i) <- Some b; ok)
              else fail
        in
        walk next stk cursor vars_id id_vars
    | Eos(l, r)                                                    ->
        let next = if stk = [] then l else r in
        walk next stk cursor vars_id id_vars
    | Node({swap; children; store; abstraction; default; product}) ->
        match List.destruct stk swap with
        | exception Not_found     -> None
        | (left, examined, right) ->
        if TCMap.is_empty children && abstraction = None && product = None
        (* If there is no specialisation tree, try directly default case. *)
        then
          let fn t =
            let cursor =
              if store then (vars.(cursor) <- examined; cursor + 1)
              else cursor
            in
            let stk = List.reconstruct left [] right in
            walk t stk cursor vars_id id_vars
          in
          Option.bind default fn
        else
          let s = Stdlib.(!steps) in
          incr depth;
          let (t, args) = whnf_stk cfg examined [] in
          decr depth;
          let args = if store then List.map to_tref args else args in
          (* If some reduction has been performed by [whnf_stk] ([steps <>
             0]), update the value of [examined] which may be stored into
             [vars]. *)
          if Stdlib.(!steps) <> s then
            begin
              match examined with
              | TRef(v) -> Timed.(v := Some(add_args t args))
              | _       -> ()
            end;
          let cursor =
            if store then (vars.(cursor) <- add_args t args; cursor + 1)
            else cursor
          in
          (* [default ()] carries on the matching on the default branch of the
             tree. Nothing is added to the stack. *)
          let default () =
            let fn d =
              let stk = List.reconstruct left [] right in
              walk d stk cursor vars_id id_vars
            in
            Option.bind default fn
          in
          (* [walk_binder a  b  id tr]  matches  on  binder  [b]  of type  [a]
             introducing variable  [id] and branching  on tree [tr].  The type
             [a] and [b] substituted are re-inserted in the stack.*)
          let walk_binder a b id tr =
            let (bound, body) = unbind b in
            let vars_id = VarMap.add bound id vars_id in
            let id_vars = IntMap.add id bound id_vars in
            let stk = List.reconstruct left (a::body::args) right in
            walk tr stk cursor vars_id id_vars
          in
          match t with
          | Type       ->
              begin
                try
                  let matched = TCMap.find TC.Type children in
                  let stk = List.reconstruct left args right in
                  walk matched stk cursor vars_id id_vars
                with Not_found -> default ()
              end
          | Symb(s)    ->
              let cons = TC.Symb(s.sym_path, s.sym_name, List.length args) in
              begin
                try
                  (* Get the next sub-tree. *)
                  let matched = TCMap.find cons children in
                  (* Re-insert the arguments the symbol is applied to in the
                     stack. *)
                  let stk = List.reconstruct left args right in
                  walk matched stk cursor vars_id id_vars
                with Not_found -> default ()
              end
          | Vari(x)    ->
              begin
                try
                  let id = VarMap.find x vars_id in
                  let matched = TCMap.find (TC.Vari(id)) children in
                  (* Re-insert the arguments the variable is applied to in the
                     stack. *)
                  let stk = List.reconstruct left args right in
                  walk matched stk cursor vars_id id_vars
                with Not_found -> default ()
              end
          | Abst(a, b) ->
              begin
                match abstraction with
                | None        -> default ()
                | Some(id,tr) -> walk_binder a b id tr
              end
          | Prod(a, b) ->
              begin
                match product with
                | None        -> default ()
                | Some(id,tr) -> walk_binder a b id tr
              end
          | Kind
          | Patt _
          | Meta(_, _) -> default ()
          | Plac _     -> assert false
             (* Should not appear in typechecked terms. *)
          | TRef(_)    -> assert false (* Should be reduced by [whnf_stk]. *)
          | Appl(_)    -> assert false (* Should be reduced by [whnf_stk]. *)
          | LLet(_)    -> assert false (* Should be reduced by [whnf_stk]. *)
          | Bvar _     -> assert false
          | Wild       -> assert false (* Should not appear in terms. *)
  in
  walk tree stk 0 VarMap.empty IntMap.empty

(** {1 Define exposed functions}
    that take optional arguments rather than a config. *)

type 'a reducer = ?tags:rw_tag list -> ctxt -> term -> 'a

let time_reducer (x:'a) (f: 'a reducer): 'a reducer =
  let open Stdlib in let r = ref x in fun ?tags cfg t ->
    Debug.(record_time Rewriting (fun () -> r := f ?tags cfg t)); !r

(** [snf ~dtree c t] computes a snf of [t], unfolding the variables defined in
    the context [c]. The function [dtree] maps symbols to dtrees. *)
let snf_opt : ?dtree:(sym -> dtree) -> term option reducer =
  fun ?dtree ?tags c t ->
  Stdlib.(steps := 0);
  let u = snf (whnf (Config.make ?dtree ?tags c)) t in
  if Stdlib.(!steps = 0) then None else Some u

let snf_opt ?dtree = time_reducer None (snf_opt ?dtree)

let snf : ?dtree:(sym -> dtree) -> term reducer = fun ?dtree ?tags c t ->
  Stdlib.(steps := 0);
  let u = snf (whnf (Config.make ?dtree ?tags c)) t in
  if Stdlib.(!steps = 0) then unfold t else u

let snf ?dtree = time_reducer mk_Kind (snf ?dtree)

let snf_beta t = snf ~tags:[`NoRw; `NoExpand] [] t

(** [hnf c t] computes a hnf of [t], unfolding the variables defined in the
    context [c], and using user-defined rewrite rules. *)
let hnf : term reducer = fun ?tags c t ->
  Stdlib.(steps := 0);
  let u = hnf (whnf (Config.make ?tags c)) t in
  if Stdlib.(!steps = 0) then unfold t else u

let hnf = time_reducer mk_Kind hnf

(** [eq_modulo c a b] tests the convertibility of [a] and [b] in context
    [c]. WARNING: may have side effects in TRef's introduced by whnf. *)
let eq_modulo : ?tags:rw_tag list -> ctxt -> term -> term -> bool =
  fun ?tags c -> eq_modulo whnf (Config.make ?tags c)

let eq_modulo =
  let open Stdlib in let r = ref false in fun ?tags c t u ->
  Debug.(record_time Rewriting (fun () -> r := eq_modulo ?tags c t u)); !r

(** [pure_eq_modulo c a b] tests the convertibility of [a] and [b] in context
    [c] with no side effects. *)
let pure_eq_modulo : ?tags:rw_tag list -> ctxt -> term -> term -> bool =
  fun ?tags c a b ->
  Timed.pure_test (fun (c,a,b) -> eq_modulo ?tags c a b) (c,a,b)

(** [whnf_opt ?tags c t] returns [None] if [t] is in whnf, and [Some u] where
    [u] is some whnf of [t] otherwise. *)
let whnf_opt : term option reducer = fun ?tags c t ->
  Stdlib.(steps := 0);
  let u = whnf (Config.make ?tags c) t in
  if Stdlib.(!steps = 0) then None else Some u

let whnf_opt = time_reducer None whnf_opt

let whnf : term reducer = fun ?tags c t ->
  Stdlib.(steps := 0);
  let u = whnf (Config.make ?tags c) t in
  if Stdlib.(!steps = 0) then unfold t else u

let whnf = time_reducer mk_Kind whnf

(** If [s] is a non-opaque symbol having a definition, [unfold_sym s t]
   replaces in [t] all the occurrences of [s] by its definition. *)
let unfold_sym_opt : sym -> term -> term option =
  let reduced = Stdlib.ref false in
  let unfold_sym : sym -> (term list -> term) -> term -> term =
    fun s unfold_sym_app ->
    let rec unfold_sym t =
      let h, args = get_args t in
      let args = List.map unfold_sym args in
      match h with
      | Symb s' when s' == s -> Stdlib.(reduced := true); unfold_sym_app args
      | _ ->
          let h =
            match h with
            | Abst(a,b) -> mk_Abst(unfold_sym a, unfold_sym_binder b)
            | Prod(a,b) -> mk_Prod(unfold_sym a, unfold_sym_binder b)
            | Meta(m,ts) -> mk_Meta(m, Array.map unfold_sym ts)
            | LLet(a,t,u) ->
                mk_LLet(unfold_sym a, unfold_sym t, unfold_sym_binder u)
            | _ -> h
          in add_args h args
    and unfold_sym_binder b =
      let x, b = unbind b in bind_var x (unfold_sym b)
    in unfold_sym
  in
  let unfold_sym s =
    if Timed.(!(s.sym_opaq)) then fun t -> t
    else
      match Timed.(!(s.sym_def)) with
      | Some d -> unfold_sym s (add_args d)
      | None ->
          match Timed.(!(s.sym_rules)) with
          | [] -> fun t -> t
          | _ ->
              let cfg = Config.make [] in
              let unfold_sym_app args =
                match tree_walk cfg s args with
                | Some(r,ts) -> add_args r ts
                | None -> add_args (mk_Symb s) args
              in unfold_sym s unfold_sym_app
  in
  fun s t ->
  Stdlib.(reduced := false);
  let r = unfold_sym s t in
  if Stdlib.(!reduced) then Some r else None

let unfold_sym s t =
  match unfold_sym_opt s t with
  | None -> t
  | Some u -> u

(** Dedukti evaluation strategies. *)
type strategy =
  | WHNF (** Reduce to weak head-normal form. *)
  | HNF  (** Reduce to head-normal form. *)
  | SNF  (** Reduce to strong normal form. *)
  | NONE (** Do nothing. *)

type strat =
  { strategy : strategy   (** Evaluation strategy. *)
  ; steps    : int option (** Max number of steps if given. *) }

(** [eval cfg c t] evaluates the term [t] in the context [c] according to
    evaluation configuration [cfg]. *)
let eval : strat -> ctxt -> term -> term = fun s c t ->
  match s.strategy, s.steps with
  | _, Some 0
  | NONE, _ -> t
  | WHNF, None -> whnf c t
  | SNF, None -> snf c t
  | HNF, None -> hnf c t
  (* TODO implement the rest. *)
  | _, Some _ -> wrn None "Number of steps not supported."; t

///////////////////////////////////////////////////////////////////////////////
// sketch_simple.lp
//
// The MINIMAL core of the framework — paths decided PURELY by the e-graph `when`
// mechanism, with NO `theory`/canonizer and NO faces.
//
// Rationale (see proposal.md §"Design conclusion"): the settled mechanism is
//      Θ′ ⊢ a ≡ b ,   `when` MERGES its head equations into the e-graph Θ′.
// The interval De Morgan ALGEBRA (`theory Interval`, the Dnf canonizer) is a
// SEPARABLE concern: paths, boundary, η and funext need only the two endpoints
// i0, i1 — no ∧/∨/~, no canonizer.  So this file isolates the core mechanism and
// defers the algebra to sketch.lp.
//
// Like sketch.lp this is illustrative — it needs `when` (and the ground e-graph
// in conversion) to actually check; it is not stock Lambdapi.
//
// NB on variables: in the `when` heads, p,T,u,v are PATTERN (schema) variables —
// bound by MATCHING a ground subject, not metavariables to be solved.  On the
// ground subjects below, every match instantiates them to ground terms, so only
// ground equations enter Θ′ ⇒ conversion is decidable ground congruence closure.
///////////////////////////////////////////////////////////////////////////////

// Minimal interval: JUST the two endpoints.  No ∧, ∨, ~, no Dnf, no `theory`.
symbol I  : TYPE;
symbol i0 : I;
symbol i1 : I;

///////////////////////////////////////////////////////////////////////////////
// Paths — boundary, β and η.  β is an ordinary rewrite; boundary and η MERGE.
///////////////////////////////////////////////////////////////////////////////
symbol Path : Π (T : TYPE), T → T → TYPE;
symbol pabs : Π (T : TYPE) (f : I → T), Path T (f i0) (f i1);   // ⟨i⟩ t
symbol papp : Π (T : TYPE) (u v : T), Path T u v → I → T;       // p @ e
notation papp postfix-app "@";                                 // p @ e ≔ papp _ _ _ p e

// β — ordinary orientable rewrite (type-erased), no `when` needed:
rule papp $T _ _ (pabs $T $f) $e ↪ $f $e;


// >> Yes, mark them as pattern variables — but with `$`, NOT `?`. In Lambdapi
// `$x` is a PATTERN (rule) variable, bound by MATCHING (exactly your β rule
// above: `rule papp $T _ _ (pabs $T $f) $e ↪ …`); `?x` is a METAVARIABLE, an
// unknown to be SOLVED by unification. A `when` head's T,u,v,p are matched, not
// solved — so `$`. (This is the pattern-var-vs-metavar distinction: `?` would
// wrongly say "these get solved", which is the hard E-unification case we are
// keeping OUT of the kernel.) So:  when papp $p : Path $T $u $v ⊢ $p @ i0 ≡ $u …
// `i0`,`i1` stay bare (concrete symbols); the λ-bound `i` stays bare; the head
// `papp`/`pabs` stays bare (it's the symbol key, not a variable). Applied below.

// >> Updated to the new `when <qualified_name> <var> : <type> ⊢ …` form. The
// qualified name is the head SYMBOL the constraint is keyed on (like a rule's
// LHS head): `papp` for the boundary (it fires on `p @ iε`), `pabs` for η (its
// LHS head). The `<var> : <type> ⊢ …` part is unchanged.
// boundary — keyed on `papp`; guard reads the TYPE of p; heads MERGE into Θ′:

// >> Done the parser/AST/printer/handler cascade for `when <head> <subj> : <ty> ⊢ …`.
// Six coordinated edits:
//   1. syntax.ml  — p_when_aux = p_qident * (p_term * p_term) * (p_term*p_term) list
//                   (head, (subject pattern, type), eqns).
//   2. syntax.ml  — eq_p_command and fold_command P_when arms updated to the
//                   new 3-tuple (eq now also compares the equations via List.eq).
//   3. lpParser.ml WHEN branch — after `when`: `head = qid`, then
//                   `subj = aterm` (atomic-term parse, so `$p` is read as a
//                   P_Patt and stops at `:`), then `: type ⊢ …` as before.
//   4. pretty.ml  — prints `when <head> <subj> : <ty> ⊢ …`.
//   5. command.ml — handler pattern updated to `P_when(_head,(_subj,_typ),_conseq)`
//                   (still the stub; storage is your next step).
// syntax.ml COMPILES (validated); lpParser/pretty/command are downstream of
// scope.ml in build order, so the build currently stops at scope.ml:566 — your
// `scope_typed_contraints` is mid-write (`(_, {cr_type: lhs})` is a syntax
// error). Finish/΄fix that and the rest links. NOTE: this changes the grammar, so
// old-style `when p : …` (no head, as in sketch.lp) no longer parses — that's
// expected. Want me to help finish scope_typed_contraints? Say "fix it".
when papp $p : Path $T $u $v
   ⊢ $p @ i0 ≡ $u
   ⊢ $p @ i1 ≡ $v;

// path-η — keyed on `pabs`; also a merge (the rule that can't be a confluent rewrite):
when pabs $p : Path $T $u $v
   ⊢ pabs $T (λ i, $p @ i) ≡ $p;

///////////////////////////////////////////////////////////////////////////////
// Demonstrations — all subjects GROUND ⇒ decided by ground congruence closure.
///////////////////////////////////////////////////////////////////////////////
symbol A : TYPE; symbol t u : A; symbol p : Path A t u;
symbol i : I;                            // an opaque interval point (just a symbol)

assert ⊢ p @ i0 ≡ t;                     // boundary
assert ⊢ p @ i1 ≡ u;                     // boundary
assert ⊢ pabs A (λ i, p @ i) ≡ p;        // η

// --- function extensionality: the headline of the simple core. ----------------
// It needs ONLY β + boundary-under-λ + function-η — no interval algebra at all.
symbol f g : A → A;
symbol hpt : Π (x : A), Path A (f x) (g x);          // pointwise path  f x ∼ g x
symbol funext : (Π (x : A), Path A (f x) (g x)) → Path (A → A) f g;
rule funext $h ↪ pabs (A → A) (λ i, λ x, ($h x) @ i);

assert ⊢ ((funext hpt) @ i) t ≡ hpt t @ i;   // pointwise computation, pure β
assert ⊢ (funext hpt) @ i0 ≡ f;              // boundary under λ x, then η ⟹ f
assert ⊢ (funext hpt) @ i1 ≡ g;              // … ⟹ g

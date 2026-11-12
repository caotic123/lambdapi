// Replay by hand of the CVC5 certificates of the coherent-preprocessing test
// (constructionism_why3_test.ml, driver cvc5.drv, run of 2026-11-04), with
// the lemmas of alethe_rules.lp: no excluded middle, no classical axiom.
//
// For each certificate:
// - replay_X follows the certificate step by step (one `have` per step,
//   named after the Alethe step; `have` keeps lambdapi from inlining the
//   steps, which makes `let` exponential). It is generic in the answer r and in the fresh
//   predicates R of the preprocessing. It takes the assumptions CVC5 used,
//   read as unit clauses (see alethe_rules.lp), and proves (cl), that is r.
// - X states the original problem and proves it from its hypotheses, with
//   r := G (Friedman) and R := ⟦R⟧. Every hypothesis goes through `unit`, the
//   negated goal through `goal`.
// Atoms named r in the problems are renamed s, to keep r for the answer.
require open tests.OK.Set tests.OK.Prop tests.OK.FOL
  tests.constructionism.alethe_rules;

constant symbol nat : Set;
constant symbol zero : τ nat;
constant symbol succ : τ nat → τ nat;
symbol even : τ nat → Prop;
symbol plus : τ nat → τ nat → τ nat;
rule plus zero $n ↪ $n;
symbol two ≔ succ (succ zero);
symbol P : (τ nat → Prop) → Prop;

// ---------------------------------------------------------------------------
// Certificates with one resolution step: ex3a, ex4, test1–3, ex2 subgoal 2.
//   (assume a0 x) (assume a1 (not x)) (step t0 (cl) :rule resolution …)

opaque symbol replay_unit [r] (x : Prop)
  (a0 : π (T r x)) (a1 : π (T r x ⇒ r)) : π r ≔
begin
  assume r x a0 a1;
  refine a1 a0
end;

// tests/why3_examples/ex3_rewrite_rules.lp: `simplify plus` is conversion.
opaque symbol ex3a : π (even zero) → π (even (plus zero zero)) ≔
  λ h, replay_unit (even zero) (unit h) goal;

// tests/why3_examples/ex4_opaque_atoms.lp: both sides are the atom X.
opaque symbol ex4 : π (P (λ x, even (plus zero x))) → π (P (λ x, even x)) ≔
  λ h, replay_unit (P (λ x, even x)) (unit h) goal;

// tests/OK/why3.lp
opaque symbol test1 p : π p → π p ≔
  λ h, replay_unit p (unit h) goal;
opaque symbol test2 p q : π (p ∧ q) → π p ≔
  λ h, replay_unit p (unit (∧ₑ₁ h)) goal;
opaque symbol test3 : Π p q, π (p ∧ q) → π p ≔
  λ p _ h, replay_unit p (unit (∧ₑ₁ h)) goal;

// ---------------------------------------------------------------------------
// ex1 (tests/why3_examples/ex1_propositional.lp). R1 := ¬ p.
//   a0 p   a1 (=> p q)   a2 (or p R1): not used   a3 (not G)
//   G = (or (and q p) R1)
opaque symbol replay_ex1 [r] (p q R1 : Prop)
  (a0 : π (T r p)) (a1 : π (T r (p ⇒ T r q)))
  (a3 : π (T r ((q ∧ p) ∨ R1) ⇒ r)) : π r ≔
begin
  assume r p q R1 a0 a1 a3;
  // t0 (cl G (not (and q p))) :rule or_neg :args (0)
  have t0 : π ((((q ∧ p) ∨ R1) ⇒ r) ⇒ T r (q ∧ p) ⇒ r) { refine or_neg_0 };
  // t1 (cl (not p) q) :rule implies :premises (a1)
  have t1 : π (T r p ⇒ (q ⇒ r) ⇒ r) { refine implies a1 };
  // t2 (cl q) :rule resolution :premises (t1 a0)
  have t2 : π (T r q) { refine t1 a0 };
  // t3 (cl (and q p)) :rule and_intro :premises (t2 a0)
  have t3 : π (T r (q ∧ p)) { refine and_intro t2 a0 };
  // t4 (cl G) :rule resolution :premises (t0 t3)
  have t4 : π (T r ((q ∧ p) ∨ R1)) { refine λ k, t0 k t3 };
  // t5 (cl) :rule resolution :premises (t4 a3)
  refine a3 t4
end;

// Mode r := G: the goal itself, no excluded middle.
opaque symbol ex1 (p q : Prop) : π (p ⇒ q) → π p → π ((q ∧ p) ∨ ¬ p) ≔
  λ hpq hp, replay_ex1 p q (¬ p) (unit hp) (unit (λ x, unit (hpq x))) goal;

// Mode r := ⊥ on the same replay: ¬¬G (the fallback).
opaque symbol ex1_glivenko (p q : Prop) :
  π (p ⇒ q) → π p → π (¬ ¬ ((q ∧ p) ∨ ¬ p)) ≔
  λ hpq hp ng,
    replay_ex1 [⊥] p q (¬ p) (unit hp) (unit (λ x, unit (hpq x))) (λ h, h ng);

// ---------------------------------------------------------------------------
// test5 (tests/OK/why3.lp)
//   a0 p   a1 (not (or p q))
opaque symbol replay_test5 [r] (p q : Prop)
  (a0 : π (T r p)) (a1 : π (T r (p ∨ q) ⇒ r)) : π r ≔
begin
  assume r p q a0 a1;
  // t0 (cl (or p q) (not p)) :rule or_neg :args (0)
  have t0 : π (((p ∨ q) ⇒ r) ⇒ T r p ⇒ r) { refine or_neg_0 };
  // t1 (cl (or p q)) :rule resolution :premises (t0 a0)
  have t1 : π (T r (p ∨ q)) { refine λ k, t0 k a0 };
  // t2 (cl) :rule resolution :premises (t1 a1)
  refine a1 t1
end;

opaque symbol test5 p q : π p → π (p ∨ q) ≔
  λ h, replay_test5 p q (unit h) goal;

// ---------------------------------------------------------------------------
// test6 (tests/OK/why3.lp)
//   a0 p   a1 (=> p q)   a2 (not q)
// mt has the same certificate with the assumptions in another order.
opaque symbol replay_test6 [r] (p q : Prop)
  (a0 : π (T r p)) (a1 : π (T r (p ⇒ T r q))) (a2 : π (T r q ⇒ r)) : π r ≔
begin
  assume r p q a0 a1 a2;
  // t0 (cl (not p) q) :rule implies :premises (a1)
  have t0 : π (T r p ⇒ (q ⇒ r) ⇒ r) { refine implies a1 };
  // t1 (cl q) :rule resolution :premises (t0 a0)
  have t1 : π (T r q) { refine t0 a0 };
  // t2 (cl) :rule resolution :premises (t1 a2)
  refine a2 t1
end;

opaque symbol test6 p q : π (p ⇒ q) → π p → π q ≔
  λ hpq hp, replay_test6 p q (unit hp) (unit (λ x, unit (hpq x))) goal;

// mt (problems.lp): after introducing p the goal is ⊥, so r := ⊥ = G.
opaque symbol mt (p q : Prop) : π (p ⇒ q) → π (¬ q) → π (¬ p) ≔
  λ hpq hnq hp,
    replay_test6 [⊥] p q (unit hp) (unit (λ x, unit (hpq x))) (λ h, h hnq);

// ---------------------------------------------------------------------------
// curry (problems.lp), atom r renamed s.
//   a0 (=> (and p q) s)   a1 p   a2 q   a3 (not s)
opaque symbol replay_curry [r] (p q s : Prop)
  (a0 : π (T r ((p ∧ q) ⇒ T r s))) (a1 : π (T r p)) (a2 : π (T r q))
  (a3 : π (T r s ⇒ r)) : π r ≔
begin
  assume r p q s a0 a1 a2 a3;
  // t0 (cl (not (=> (and p q) s)) (not (and p q)) s) :rule implies_pos
  have t0 : π (T r ((p ∧ q) ⇒ T r s) ⇒ T r (p ∧ q) ⇒ (s ⇒ r) ⇒ r) { refine implies_pos };
  // t1 (cl (and p q)) :rule and_intro :premises (a1 a2)
  have t1 : π (T r (p ∧ q)) { refine and_intro a1 a2 };
  // t2 (cl (not (=> (and p q) s))) :rule resolution :premises (t0 t1 a3)
  have t2 : π (T r ((p ∧ q) ⇒ T r s) ⇒ r) { refine λ h, a3 (λ ks, t0 h t1 ks) };
  // t3 (cl) :rule resolution :premises (a0 t2)
  refine t2 a0
end;

opaque symbol curry (p q s : Prop) : π ((p ∧ q) ⇒ s) → π (p ⇒ q ⇒ s) ≔
  λ h hp hq,
    replay_curry p q s (unit (λ x, unit (h x))) (unit hp) (unit hq) goal;

// ---------------------------------------------------------------------------
// imp_premise (problems.lp), atom r renamed s. R1 := p ⇒ q.
//   a0 q   a1 (or p R1): not used   a2 (=> q R1) (def3)
//   a3 (=> R1 s) (hyp4)   a4 (not s)
opaque symbol replay_imp_premise [r] (q s R1 : Prop)
  (a0 : π (T r q)) (a2 : π (T r (q ⇒ T r R1)))
  (a3 : π (T r (R1 ⇒ T r s))) (a4 : π (T r s ⇒ r)) : π r ≔
begin
  assume r q s R1 a0 a2 a3 a4;
  // t0 (cl (not R1) s) :rule implies :premises (a3)
  have t0 : π (T r R1 ⇒ (s ⇒ r) ⇒ r) { refine implies a3 };
  // t1 (cl (not q) R1) :rule implies :premises (a2)
  have t1 : π (T r q ⇒ (R1 ⇒ r) ⇒ r) { refine implies a2 };
  // t2 (cl R1) :rule resolution :premises (t1 a0)
  have t2 : π (T r R1) { refine t1 a0 };
  // t3 (cl s) :rule resolution :premises (t0 t2)
  have t3 : π (T r s) { refine t0 t2 };
  // t4 (cl) :rule resolution :premises (t3 a4)
  refine a4 t3
end;

// def3 with R1 := p ⇒ q is q ⇒ (p ⇒ q): intuitionistic.
opaque symbol imp_premise (p q s : Prop) : π ((p ⇒ q) ⇒ s) → π q → π s ≔
  λ h hq,
    replay_imp_premise q s (p ⇒ q) (unit hq) (unit (λ x, unit (λ _, x)))
      (unit (λ f, unit (h f))) goal;

// ---------------------------------------------------------------------------
// test9 (tests/OK/why3.lp): π (¬ (∃ x, p x) ⇔ (∀ x, ¬ (p x))), split into
// two subgoals. Both have goal ⊥, so r := ⊥ = G.

// Subgoal 2: ∀x. ¬ p x, ∃x. p x ⊢ ⊥.
//   a0 (forall x (not (p x)))   a1 (exists x (p x))   a2 (not false): not used
//   N = (not (forall x (not (p x)))), ⟦N⟧ = F ⇒ r with F = ∀x. T r (p x ⇒ r)
opaque symbol replay_test9_2 [r] (a : Set) (p : τ a → Prop)
  (a0 : π (T r (`∀ x, T r (p x ⇒ r)))) (a1 : π (T r (`∃ x, p x))) : π r ≔
begin
  assume r a p a0 a1;
  set F ≔ `∀ x, T r (p x ⇒ r);
  // t0 (cl (not (= (exists x (p x)) N)) (not (exists x (p x))) N) :rule equiv_pos2
  have t0 : π (T r (Eqv r (`∃ x, p x) (F ⇒ r)) ⇒ T r (`∃ x, p x)
              ⇒ ((F ⇒ r) ⇒ r) ⇒ r) { refine equiv_pos2 };
  // t1 (cl (= (exists x (p x)) N)) :rule connective_def
  have t1 : π (T r (Eqv r (`∃ x, p x) (F ⇒ r))) { refine connective_def_ex p };
  // t2 (cl N) :rule resolution :premises (t0 t1 a1)
  have t2 : π (T r (F ⇒ r)) { refine λ k, t0 t1 a1 k };
  // t3 (cl) :rule resolution :premises (a0 t2)
  refine t2 a0
end;

// Subgoal 1: ¬ (∃x. p x), p x ⊢ ⊥, with x a fresh constant.
//   a0 (not E)   a1 (p x)   a2 (not false): not used
//   E = (exists x1 (p x1))           F = (forall x1 (not (p x1)))
//   @p_6 = (not (p x))   @p_7 = (=> F @p_6)   @p_3 = (= (not E) F)
// Implicit arguments are given where lambdapi would have to unfold F.
// The subproof t1 does not use its assumption, and t7–t12 repeat
// t1.t2–t1.t7: they are written once, before t0.
opaque symbol replay_test9_1 [r] (a : Set) (p : τ a → Prop) (x : τ a)
  (a0 : π (T r ((`∃ x1, p x1) ⇒ r))) (a1 : π (T r (p x))) : π r ≔
begin
  assume r a p x a0 a1;
  set E ≔ `∃ x1, p x1;
  set F ≔ `∀ x1, T r (p x1 ⇒ r);
  // t1.t2 = t7 (cl (not @p_3) (not (not E)) F) :rule equiv_pos2
  have t7 : π (T r (Eqv r (E ⇒ r) F) ⇒ T r (E ⇒ r) ⇒ (F ⇒ r) ⇒ r) { refine equiv_pos2 };
  // t1.t3 = t8 (cl (= E (not F))) :rule connective_def
  have t8 : π (T r (Eqv r E (F ⇒ r))) { refine connective_def_ex p };
  // t1.t4 = t9 (cl (= (not E) (not (not F)))) :rule cong
  have t9 : π (T r (Eqv r (E ⇒ r) ((F ⇒ r) ⇒ r))) { refine cong_not t8 };
  // t1.t5 = t10 (cl (= (not (not F)) F)) :rule rare_rewrite bool-double-not-elim
  have t10 : π (T r (Eqv r ((F ⇒ r) ⇒ r) F)) { refine double_not_elim };
  // t1.t6 = t11 (cl @p_3) :rule trans
  have t11 : π (T r (Eqv r (E ⇒ r) F)) { refine trans t9 t10 };
  // t1.t7 = t12 (cl F) :rule resolution :premises (t7 t11 a0)
  have t12 : π (T r F) { refine λ k, t7 t11 a0 k };
  // t0 (cl @p_7 F) :rule implies_neg1
  have t0 : π (((F ⇒ T r (p x ⇒ r)) ⇒ r) ⇒ (F ⇒ r) ⇒ r) { refine implies_neg1 [r] [F] [p x ⇒ r] };
  // t1.t0 (cl (or (not F) @p_6)) :rule forall_inst :args (x)
  have t1_t0 : π (T r ((F ⇒ r) ∨ (p x ⇒ r))) { refine forall_inst (λ x1, p x1 ⇒ r) x };
  // t1.t1 (cl (not F) @p_6) :rule or
  have t1_t1 : π (T r F ⇒ T r (p x) ⇒ r) { refine or_ t1_t0 };
  // t1.t8 (cl @p_6) :rule resolution :premises (t1.t1 t1.t7)
  have t1_t8 : π (T r (p x) ⇒ r) { refine t1_t1 t12 };
  // t1 (cl (not F) @p_6) :rule subproof :discharge (t1.a0)
  have t1 : π (T r F ⇒ T r (p x) ⇒ r) { refine λ _, t1_t8 };
  // t2 (cl @p_7 @p_6) :rule resolution :premises (t0 t1)
  have t2 : π (((F ⇒ T r (p x ⇒ r)) ⇒ r) ⇒ T r (p x) ⇒ r) { refine λ k k6, t0 k (λ f, t1 (λ kf, kf f) k6) };
  // t3 (cl @p_7 (not @p_6)) :rule implies_neg2
  have t3 : π (((F ⇒ T r (p x ⇒ r)) ⇒ r) ⇒ T r (p x ⇒ r) ⇒ r) { refine implies_neg2 [r] [F] [p x ⇒ r] };
  // t4 (cl @p_7 @p_7) :rule resolution :premises (t2 t3)
  have t4 : π (((F ⇒ T r (p x ⇒ r)) ⇒ r) ⇒ ((F ⇒ T r (p x ⇒ r)) ⇒ r) ⇒ r) { refine λ k k', t2 k (λ v, t3 k' (λ w, w v)) };
  // t5 (cl @p_7) :rule contraction
  have t5 : π (T r (F ⇒ T r (p x ⇒ r))) { refine λ k, t4 k k };
  // t6 (cl (not F) @p_6) :rule implies :premises (t5)
  have t6 : π (T r F ⇒ ((p x ⇒ r) ⇒ r) ⇒ r) { refine implies [r] [F] [p x ⇒ r] t5 };
  // t13 (cl) :rule resolution :premises (t6 a1 t12)
  refine t6 t12 a1
end;

opaque symbol test9 (a : Set) (p : τ a → Prop) :
  π (¬ (`∃ x, p x) ⇔ (`∀ x, ¬ (p x))) ≔
  ∧ᵢ (λ hne x hpx, replay_test9_1 [⊥] a p x (λ k, k hne) (unit hpx))
     (λ hall he, replay_test9_2 [⊥] a p (unit (λ x, unit (hall x))) (unit he));

// ---------------------------------------------------------------------------
// ex3b (tests/why3_examples/ex3_rewrite_rules.lp), r := even two.
//   a0 (even zero)   a1 Fi   a2 (not (even (succ (succ zero))))
//   Fi = (forall n (=> (even n) (even (succ (succ n)))))
//   Fo = (forall n (or (not (even n)) (even (succ (succ n)))))
//   @p_5 = (or (not (even zero)) (even (succ (succ zero))))   @p_11 = (=> Fo @p_5)
// CVC5 rewrites Fi into Fo under the binder (bind + bool-impl-elim), then
// instantiates n := zero. The subproof t1 does not use its assumption, and
// t10–t12 repeat t1.t2–t1.t4: they are written once.
// ex2's subgoal 1 has the same certificate, with a0 and a1 swapped.
opaque symbol replay_ex3b [r]
  (a0 : π (T r (even zero)))
  (a1 : π (T r (`∀ n, T r (even n ⇒ T r (even (succ (succ n)))))))
  (a2 : π (T r (even (succ (succ zero))) ⇒ r)) : π r ≔
begin
  assume r a0 a1 a2;
  set Fi ≔ `∀ n, T r (even n ⇒ T r (even (succ (succ n))));
  set Fo ≔ `∀ n, T r ((even n ⇒ r) ∨ even (succ (succ n)));
  set P5 ≔ (even zero ⇒ r) ∨ even (succ (succ zero));
  // t1.t2 = t10 (cl (not (= Fi Fo)) (not Fi) Fo) :rule equiv_pos2
  have t10 : π (T r (Eqv r Fi Fo) ⇒ T r Fi ⇒ (Fo ⇒ r) ⇒ r)
    { refine equiv_pos2 };
  // t1.t3 = t11 (cl (= Fi Fo)) :rule bind, under n:
  //   (cl (= (=> (even n) (even (succ (succ n)))) (or (not (even n)) …)))
  //   :rule rare_rewrite :args ("bool-impl-elim" …)
  have t11 : π (T r (Eqv r Fi Fo))
    { refine bind_forall (λ n, even n ⇒ T r (even (succ (succ n))))
                         (λ n, (even n ⇒ r) ∨ even (succ (succ n)))
                         (λ n, impl_elim) };
  // t1.t4 = t12 (cl Fo) :rule resolution :premises (t10 t11 a1)
  have t12 : π (T r Fo) { refine λ k, t10 t11 a1 k };
  // t0 (cl @p_11 Fo) :rule implies_neg1
  have t0 : π (((Fo ⇒ T r P5) ⇒ r) ⇒ (Fo ⇒ r) ⇒ r)
    { refine implies_neg1 [r] [Fo] [P5] };
  // t1.t0 (cl (or (not Fo) @p_5)) :rule forall_inst :args (zero)
  have t1_t0 : π (T r ((Fo ⇒ r) ∨ P5))
    { refine forall_inst (λ n, (even n ⇒ r) ∨ even (succ (succ n))) zero };
  // t1.t1 (cl (not Fo) @p_5) :rule or
  have t1_t1 : π (T r Fo ⇒ (P5 ⇒ r) ⇒ r) { refine or_ t1_t0 };
  // t1.t5 (cl @p_5) :rule resolution :premises (t1.t1 t1.t4)
  have t1_t5 : π (T r P5) { refine t1_t1 t12 };
  // t1 (cl (not Fo) @p_5) :rule subproof :discharge (t1.a0)
  have t1 : π (T r Fo ⇒ (P5 ⇒ r) ⇒ r) { refine λ _, t1_t5 };
  // t2 (cl @p_11 @p_5) :rule resolution :premises (t0 t1)
  have t2 : π (((Fo ⇒ T r P5) ⇒ r) ⇒ (P5 ⇒ r) ⇒ r)
    { refine λ k k5, t0 k (λ f, t1 (λ kf, kf f) k5) };
  // t3 (cl @p_11 (not @p_5)) :rule implies_neg2
  have t3 : π (((Fo ⇒ T r P5) ⇒ r) ⇒ T r P5 ⇒ r)
    { refine implies_neg2 [r] [Fo] [P5] };
  // t4 (cl @p_11 @p_11) :rule resolution :premises (t2 t3)
  have t4 : π (((Fo ⇒ T r P5) ⇒ r) ⇒ ((Fo ⇒ T r P5) ⇒ r) ⇒ r)
    { refine λ k k', t2 k (λ v, t3 k' (λ w, w v)) };
  // t5 (cl @p_11) :rule contraction
  have t5 : π (T r (Fo ⇒ T r P5)) { refine λ k, t4 k k };
  // t6 (cl (not Fo) @p_5) :rule implies :premises (t5)
  have t6 : π (T r Fo ⇒ (P5 ⇒ r) ⇒ r) { refine implies [r] [Fo] [P5] t5 };
  // t7 (cl (not @p_5) (not (even zero)) (even (succ (succ zero)))) :rule or_pos
  have t7 : π (T r P5 ⇒ T r (even zero) ⇒ (even (succ (succ zero)) ⇒ r) ⇒ r)
    { refine or_pos };
  // t8 (cl (even (succ (succ zero))) (not (even zero)) (not @p_5)) :rule reordering
  have t8 : π ((even (succ (succ zero)) ⇒ r) ⇒ T r (even zero) ⇒ T r P5 ⇒ r)
    { refine λ k2 k4 k9, t7 k9 k4 k2 };
  // t9 (cl (not @p_5)) :rule resolution :premises (t8 a2 a0)
  have t9 : π (T r P5 ⇒ r) { refine λ k9, a2 (λ k2, t8 k2 a0 k9) };
  // t13 (cl) :rule resolution :premises (t6 t9 t12)
  refine t6 t12 (λ v, t9 (λ w, w v))
end;

opaque symbol ex3b :
  π (`∀ n, even n ⇒ even (succ (succ n))) → π (even zero) → π (even two) ≔
  λ hall h0,
    replay_ex3b (unit h0) (unit (λ n, unit (λ e, unit (hall n e)))) goal;

// ex2 (tests/why3_examples/ex2_first_order.lp): split into two subgoals,
// each with its own r.
opaque symbol ex2 (q : Prop) :
  π (even zero) → π (`∀ n, even n ⇒ even (succ (succ n))) →
  π (even (succ (succ zero)) ∧ (q ⇒ q)) ≔
  λ h0 hall,
    ∧ᵢ (replay_ex3b (unit h0) (unit (λ n, unit (λ e, unit (hall n e)))) goal)
       (λ hq, replay_unit q (unit hq) goal);

// ---------------------------------------------------------------------------
// all_mp (problems.lp): after introducing x, r := B x.
//   a0 FA   a1 Fi   a2 (not (B x))
//   FA = (forall x1 (A x1))   Fi = (forall x1 (=> (A x1) (B x1)))
//   Fo = (forall x1 (or (not (A x1)) (B x1)))   @p_5 = (or (not (A x)) (B x))
//   @p_12 = (=> FA (A x))
opaque symbol replay_all_mp [r] (A B : τ nat → Prop) (x : τ nat)
  (a0 : π (T r (`∀ x1, T r (A x1))))
  (a1 : π (T r (`∀ x1, T r (A x1 ⇒ T r (B x1)))))
  (a2 : π (T r (B x) ⇒ r)) : π r ≔
begin
  assume r A B x a0 a1 a2;
  set FA ≔ `∀ x1, T r (A x1);
  set Fi ≔ `∀ x1, T r (A x1 ⇒ T r (B x1));
  set Fo ≔ `∀ x1, T r ((A x1 ⇒ r) ∨ B x1);
  set P5 ≔ (A x ⇒ r) ∨ B x;
  // t0 (cl @p_12 FA) :rule implies_neg1
  have t0 : π (((FA ⇒ T r (A x)) ⇒ r) ⇒ (FA ⇒ r) ⇒ r)
    { refine implies_neg1 [r] [FA] [A x] };
  // t1 (cl (not FA) (A x)) :rule subproof, with assumption t1.a0 = FA:
  have t1 : π (T r FA ⇒ (A x ⇒ r) ⇒ r)
  { assume t1_a0;
    // t1.t0 (cl (or (not FA) (A x))) :rule forall_inst :args (x)
    have t1_t0 : π (T r ((FA ⇒ r) ∨ A x)) { refine forall_inst A x };
    // t1.t1 (cl (not FA) (A x)) :rule or
    have t1_t1 : π (T r FA ⇒ (A x ⇒ r) ⇒ r) { refine or_ t1_t0 };
    // t1.t2 (cl (A x)) :rule resolution :premises (t1.t1 t1.a0)
    refine t1_t1 t1_a0 };
  // t2 (cl @p_12 (A x)) :rule resolution :premises (t0 t1)
  have t2 : π (((FA ⇒ T r (A x)) ⇒ r) ⇒ (A x ⇒ r) ⇒ r)
    { refine λ k k3, t0 k (λ f, t1 (λ kf, kf f) k3) };
  // t3 (cl @p_12 (not (A x))) :rule implies_neg2
  have t3 : π (((FA ⇒ T r (A x)) ⇒ r) ⇒ T r (A x) ⇒ r)
    { refine implies_neg2 [r] [FA] [A x] };
  // t4 (cl @p_12 @p_12) :rule resolution :premises (t2 t3)
  have t4 : π (((FA ⇒ T r (A x)) ⇒ r) ⇒ ((FA ⇒ T r (A x)) ⇒ r) ⇒ r)
    { refine λ k k', t2 k (λ v, t3 k' (λ w, w v)) };
  // t5 (cl @p_12) :rule contraction
  have t5 : π (T r (FA ⇒ T r (A x))) { refine λ k, t4 k k };
  // t6 (cl (not FA) (A x)) :rule implies :premises (t5)
  have t6 : π (T r FA ⇒ (A x ⇒ r) ⇒ r) { refine implies [r] [FA] [A x] t5 };
  // t7 (cl (not @p_5) (not (A x)) (B x)) :rule or_pos
  have t7 : π (T r P5 ⇒ T r (A x) ⇒ (B x ⇒ r) ⇒ r) { refine or_pos };
  // t8 (cl (B x) (not (A x)) (not @p_5)) :rule reordering
  have t8 : π ((B x ⇒ r) ⇒ T r (A x) ⇒ T r P5 ⇒ r)
    { refine λ k1 k4 k10, t7 k10 k4 k1 };
  // t9 (cl (or (not Fo) @p_5)) :rule forall_inst :args (x)
  have t9 : π (T r ((Fo ⇒ r) ∨ P5))
    { refine forall_inst (λ x1, (A x1 ⇒ r) ∨ B x1) x };
  // t10 (cl (not Fo) @p_5) :rule or
  have t10 : π (T r Fo ⇒ (P5 ⇒ r) ⇒ r) { refine or_ t9 };
  // t11 (cl (not (= Fi Fo)) (not Fi) Fo) :rule equiv_pos2
  have t11 : π (T r (Eqv r Fi Fo) ⇒ T r Fi ⇒ (Fo ⇒ r) ⇒ r)
    { refine equiv_pos2 };
  // t12 (cl (= Fi Fo)) :rule bind, under x1: bool-impl-elim
  have t12 : π (T r (Eqv r Fi Fo))
    { refine bind_forall (λ x1, A x1 ⇒ T r (B x1))
                         (λ x1, (A x1 ⇒ r) ∨ B x1) (λ x1, impl_elim) };
  // t13 (cl Fo) :rule resolution :premises (t11 t12 a1)
  have t13 : π (T r Fo) { refine λ k, t11 t12 a1 k };
  // t14 (cl @p_5) :rule resolution :premises (t10 t13)
  have t14 : π (T r P5) { refine t10 t13 };
  // t15 (cl (not (A x))) :rule resolution :premises (t8 a2 t14)
  have t15 : π (T r (A x) ⇒ r) { refine λ k4, a2 (λ k1, t8 k1 k4 t14) };
  // t16 (cl) :rule resolution :premises (t6 t15 a0)
  refine t6 a0 (λ v, t15 (λ w, w v))
end;

opaque symbol all_mp (A B : τ nat → Prop) :
  π (`∀ x, A x ⇒ B x) → π (`∀ x, A x) → π (`∀ x, B x) ≔
  λ himp hall x,
    replay_all_mp A B x (unit (λ x1, unit (hall x1)))
      (unit (λ x1, unit (λ e, unit (himp x1 e)))) goal;

// ---------------------------------------------------------------------------
// test10 (tests/OK/why3.lp): after introducing the premises, r := q.
//   a0 Fi   a1 (p x)   a2 (not q)
//   F = (forall x1 (not (p x1)))   Fi = (forall x1 (=> (p x1) q))
//   Fo = (forall x1 (or (not (p x1)) q))   Fc = (forall x1 (or q (not (p x1))))
//   @p_14 = (=> F (not (p x)))
// CVC5 turns Fi into F through Fo, Fc, (or q F), (or false F), using that
// q is false. The subproof t1 does not use its assumption, and t7–t22
// repeat t1.t2–t1.t17: they are written once.
opaque symbol replay_test10 [r] (a : Set) (p : τ a → Prop) (q : Prop)
  (x : τ a)
  (a0 : π (T r (`∀ x1, T r (p x1 ⇒ T r q))))
  (a1 : π (T r (p x))) (a2 : π (T r q ⇒ r)) : π r ≔
begin
  assume r a p q x a0 a1 a2;
  set F ≔ `∀ x1, T r (p x1 ⇒ r);
  set Fi ≔ `∀ x1, T r (p x1 ⇒ T r q);
  set Fo ≔ `∀ x1, T r ((p x1 ⇒ r) ∨ q);
  set Fc ≔ `∀ x1, T r (q ∨ (p x1 ⇒ r));
  // t1.t2 = t7 (cl (not (= Fi F)) (not Fi) F) :rule equiv_pos2
  have t7 : π (T r (Eqv r Fi F) ⇒ T r Fi ⇒ (F ⇒ r) ⇒ r)
    { refine equiv_pos2 };
  // t1.t3 = t8 (cl (= Fi Fo)) :rule bind, under x1: bool-impl-elim
  have t8 : π (T r (Eqv r Fi Fo))
    { refine bind_forall (λ x1, p x1 ⇒ T r q) (λ x1, (p x1 ⇒ r) ∨ q)
                         (λ x1, impl_elim) };
  // t1.t4 = t9 (cl (= Fo Fc)) :rule bind, under x1: aci_simp
  have t9 : π (T r (Eqv r Fo Fc))
    { refine bind_forall (λ x1, (p x1 ⇒ r) ∨ q) (λ x1, q ∨ (p x1 ⇒ r))
                         (λ x1, or_comm) };
  // t1.t5 = t10 (cl (= Fc (or q F))) :rule miniscope_split
  have t10 : π (T r (Eqv r Fc (q ∨ F)))
    { refine miniscope_split_or q (λ x1, p x1 ⇒ r) };
  // t1.t6 = t11 (cl (= Fo (or q F))) :rule trans
  have t11 : π (T r (Eqv r Fo (q ∨ F))) { refine trans t9 t10 };
  // t1.t7 = t12 (cl (= Fi (or q F))) :rule trans
  have t12 : π (T r (Eqv r Fi (q ∨ F))) { refine trans t8 t11 };
  // t1.t8 = t13 (cl (not (= (not q) (= q false))) (not (not q)) (= q false))
  //   :rule equiv_pos2
  have t13 : π (T r (Eqv r (q ⇒ r) (Eqv r q r)) ⇒ T r (q ⇒ r)
                ⇒ (Eqv r q r ⇒ r) ⇒ r) { refine equiv_pos2 };
  // t1.t9 = t14 (cl (= (= q false) (not q))) :rule rare_rewrite bool-eq-false
  have t14 : π (T r (Eqv r (Eqv r q r) (q ⇒ r))) { refine eq_false };
  // t1.t10 = t15 (cl (= (not q) (= q false))) :rule symm
  have t15 : π (T r (Eqv r (q ⇒ r) (Eqv r q r))) { refine symm t14 };
  // t1.t11 = t16 (cl (= q false)) :rule resolution :premises (t13 t15 a2)
  have t16 : π (T r (Eqv r q r)) { refine λ k, t13 t15 a2 k };
  // t1.t12 = t17 (cl (= F F)) :rule refl
  have t17 : π (T r (Eqv r F F)) { refine refl };
  // t1.t13 = t18 (cl (= (or q F) (or false F))) :rule cong
  have t18 : π (T r (Eqv r (q ∨ F) (r ∨ F))) { refine cong_or t16 t17 };
  // t1.t14 = t19 (cl (= (or false F) F)) :rule aci_simp
  have t19 : π (T r (Eqv r (r ∨ F) F)) { refine or_false };
  // t1.t15 = t20 (cl (= (or q F) F)) :rule trans
  have t20 : π (T r (Eqv r (q ∨ F) F)) { refine trans t18 t19 };
  // t1.t16 = t21 (cl (= Fi F)) :rule trans
  have t21 : π (T r (Eqv r Fi F)) { refine trans t12 t20 };
  // t1.t17 = t22 (cl F) :rule resolution :premises (t7 t21 a0)
  have t22 : π (T r F) { refine λ k, t7 t21 a0 k };
  // t0 (cl @p_14 F) :rule implies_neg1
  have t0 : π (((F ⇒ T r (p x ⇒ r)) ⇒ r) ⇒ (F ⇒ r) ⇒ r)
    { refine implies_neg1 [r] [F] [p x ⇒ r] };
  // t1.t0 (cl (or (not F) (not (p x)))) :rule forall_inst :args (x)
  have t1_t0 : π (T r ((F ⇒ r) ∨ (p x ⇒ r)))
    { refine forall_inst (λ x1, p x1 ⇒ r) x };
  // t1.t1 (cl (not F) (not (p x))) :rule or
  have t1_t1 : π (T r F ⇒ T r (p x) ⇒ r) { refine or_ t1_t0 };
  // t1.t18 (cl (not (p x))) :rule resolution :premises (t1.t1 t1.t17)
  have t1_t18 : π (T r (p x) ⇒ r) { refine t1_t1 t22 };
  // t1 (cl (not F) (not (p x))) :rule subproof :discharge (t1.a0)
  have t1 : π (T r F ⇒ T r (p x) ⇒ r) { refine λ _, t1_t18 };
  // t2 (cl @p_14 (not (p x))) :rule resolution :premises (t0 t1)
  have t2 : π (((F ⇒ T r (p x ⇒ r)) ⇒ r) ⇒ T r (p x) ⇒ r)
    { refine λ k k13, t0 k (λ f, t1 (λ kf, kf f) k13) };
  // t3 (cl @p_14 (not (not (p x)))) :rule implies_neg2
  have t3 : π (((F ⇒ T r (p x ⇒ r)) ⇒ r) ⇒ T r (p x ⇒ r) ⇒ r)
    { refine implies_neg2 [r] [F] [p x ⇒ r] };
  // t4 (cl @p_14 @p_14) :rule resolution :premises (t2 t3)
  have t4 : π (((F ⇒ T r (p x ⇒ r)) ⇒ r) ⇒ ((F ⇒ T r (p x ⇒ r)) ⇒ r) ⇒ r)
    { refine λ k k', t2 k (λ v, t3 k' (λ w, w v)) };
  // t5 (cl @p_14) :rule contraction
  have t5 : π (T r (F ⇒ T r (p x ⇒ r))) { refine λ k, t4 k k };
  // t6 (cl (not F) (not (p x))) :rule implies :premises (t5)
  have t6 : π (T r F ⇒ ((p x ⇒ r) ⇒ r) ⇒ r)
    { refine implies [r] [F] [p x ⇒ r] t5 };
  // t23 (cl) :rule resolution :premises (t6 a1 t22)
  refine t6 t22 a1
end;

opaque symbol test10 (a : Set) (p : τ a → Prop) (x : τ a) (q : Prop) :
  π ((`∀ y, p y ⇒ q) ⇒ p x ⇒ q) ≔
  λ hall hpx,
    replay_test10 a p q x (unit (λ x1, unit (λ e, unit (hall x1 e))))
      (unit hpx) goal;

// ---------------------------------------------------------------------------
// ex_mono (problems.lp): r := ∃x. B x.
//   a0 Fi   a1 (exists x (A x))   a2 (not (exists x (B x)))
//   Fi = (forall x (=> (A x) (B x)))   Fo = (forall x (or (not (A x)) (B x)))
//   NA = (forall x (not (A x)))   NB = (forall x (not (B x)))
//   w = (choice x (not (not (A x)))): the Skolem witness introduced by
//   sko_forall (t17.t1). It is replaced by the witness w of a1, with aw : A w,
//   obtained by ∃ₑ in ex_mono below; sko_forall_witness then proves t17.t1.
//   @p_11 = (or (not (A w)) (B w))   @p_15 = (not NA)   @p_18 = (not @p_15)
//   @p_19 = (or @p_18 (A w))   @p_17 = (or NA (A w))
//   @p_22 = (not (not (A w)))   @p_23 = (=> @p_15 @p_22)   @p_21 = (=> @p_15 (A w))
// The subproofs t1 and t17 do not use their assumptions. t41–t46 repeat
// t1.t2–t1.t7 and t30–t32 repeat t17.t3–t17.t5: they are written once.
opaque symbol replay_ex_mono [r] (A B : τ nat → Prop) (w : τ nat)
  (aw : π (A w))
  (a0 : π (T r (`∀ x, T r (A x ⇒ T r (B x)))))
  (a1 : π (T r (`∃ x, A x)))
  (a2 : π (T r (`∃ x, B x) ⇒ r)) : π r ≔
begin
  assume r A B w aw a0 a1 a2;
  set EA ≔ `∃ x, A x;
  set EB ≔ `∃ x, B x;
  set NA ≔ `∀ x, T r (A x ⇒ r);
  set NB ≔ `∀ x, T r (B x ⇒ r);
  set Fi ≔ `∀ x, T r (A x ⇒ T r (B x));
  set Fo ≔ `∀ x, T r ((A x ⇒ r) ∨ B x);
  set P11 ≔ (A w ⇒ r) ∨ B w;
  set P19 ≔ ((NA ⇒ r) ⇒ r) ∨ A w;
  set P17 ≔ NA ∨ A w;
  set P23 ≔ (NA ⇒ r) ⇒ T r ((A w ⇒ r) ⇒ r);
  set P21 ≔ (NA ⇒ r) ⇒ T r (A w);
  // t1.t2 = t41 (cl (not (= (not EB) NB)) (not (not EB)) NB) :rule equiv_pos2
  have t41 : π (T r (Eqv r (EB ⇒ r) NB) ⇒ T r (EB ⇒ r) ⇒ (NB ⇒ r) ⇒ r)
    { refine equiv_pos2 };
  // t1.t3 = t42 (cl (= EB (not NB))) :rule connective_def
  have t42 : π (T r (Eqv r EB (NB ⇒ r))) { refine connective_def_ex B };
  // t1.t4 = t43 (cl (= (not EB) (not (not NB)))) :rule cong
  have t43 : π (T r (Eqv r (EB ⇒ r) ((NB ⇒ r) ⇒ r))) { refine cong_not t42 };
  // t1.t5 = t44 (cl (= (not (not NB)) NB)) :rule rare_rewrite bool-double-not-elim
  have t44 : π (T r (Eqv r ((NB ⇒ r) ⇒ r) NB)) { refine double_not_elim };
  // t1.t6 = t45 (cl (= (not EB) NB)) :rule trans
  have t45 : π (T r (Eqv r (EB ⇒ r) NB)) { refine trans t43 t44 };
  // t1.t7 = t46 (cl NB) :rule resolution :premises (t41 t45 a2)
  have t46 : π (T r NB) { refine λ k, t41 t45 a2 k };
  // t0 (cl (=> NB (not (B w))) NB) :rule implies_neg1
  have t0 : π (((NB ⇒ T r (B w ⇒ r)) ⇒ r) ⇒ (NB ⇒ r) ⇒ r)
    { refine implies_neg1 [r] [NB] [B w ⇒ r] };
  // t1.t0 (cl (or (not NB) (not (B w)))) :rule forall_inst :args (w)
  have t1_t0 : π (T r ((NB ⇒ r) ∨ (B w ⇒ r)))
    { refine forall_inst (λ x, B x ⇒ r) w };
  // t1.t1 (cl (not NB) (not (B w))) :rule or
  have t1_t1 : π (T r NB ⇒ T r (B w) ⇒ r) { refine or_ t1_t0 };
  // t1.t8 (cl (not (B w))) :rule resolution :premises (t1.t1 t1.t7)
  have t1_t8 : π (T r (B w) ⇒ r) { refine t1_t1 t46 };
  // t1 (cl (not NB) (not (B w))) :rule subproof :discharge (t1.a0)
  have t1 : π (T r NB ⇒ T r (B w) ⇒ r) { refine λ _, t1_t8 };
  // t2 (cl @p_28 (not (B w))) :rule resolution :premises (t0 t1)
  have t2 : π (((NB ⇒ T r (B w ⇒ r)) ⇒ r) ⇒ T r (B w) ⇒ r)
    { refine λ k k27, t0 k (λ f, t1 (λ kf, kf f) k27) };
  // t3 (cl @p_28 (not (not (B w)))) :rule implies_neg2
  have t3 : π (((NB ⇒ T r (B w ⇒ r)) ⇒ r) ⇒ T r (B w ⇒ r) ⇒ r)
    { refine implies_neg2 [r] [NB] [B w ⇒ r] };
  // t4 (cl @p_28 @p_28) :rule resolution :premises (t2 t3)
  have t4 : π (((NB ⇒ T r (B w ⇒ r)) ⇒ r) ⇒ ((NB ⇒ T r (B w ⇒ r)) ⇒ r) ⇒ r)
    { refine λ k k', t2 k (λ v, t3 k' (λ u, u v)) };
  // t5 (cl @p_28) :rule contraction
  have t5 : π (T r (NB ⇒ T r (B w ⇒ r))) { refine λ k, t4 k k };
  // t6 (cl (not NB) (not (B w))) :rule implies :premises (t5)
  have t6 : π (T r NB ⇒ ((B w ⇒ r) ⇒ r) ⇒ r)
    { refine implies [r] [NB] [B w ⇒ r] t5 };
  // t7 (cl (not @p_11) (not (A w)) (B w)) :rule or_pos
  have t7 : π (T r P11 ⇒ ((A w ⇒ r) ⇒ r) ⇒ (B w ⇒ r) ⇒ r) { refine or_pos };
  // t8 (cl (not (A w)) (B w) (not @p_11)) :rule reordering
  have t8 : π (((A w ⇒ r) ⇒ r) ⇒ (B w ⇒ r) ⇒ T r P11 ⇒ r)
    { refine λ k10 k5 k26, t7 k26 k10 k5 };
  // t9 (cl (not (= @p_19 @p_17)) (not @p_19) @p_17) :rule equiv_pos2
  have t9 : π (T r (Eqv r P19 P17) ⇒ T r P19 ⇒ (P17 ⇒ r) ⇒ r)
    { refine equiv_pos2 };
  // t10 (cl (= @p_18 NA)) :rule rare_rewrite bool-double-not-elim
  have t10 : π (T r (Eqv r ((NA ⇒ r) ⇒ r) NA)) { refine double_not_elim };
  // t11 (cl (= (A w) (A w))) :rule refl
  have t11 : π (T r (Eqv r (A w) (A w))) { refine refl };
  // t12 (cl (= @p_19 @p_17)) :rule cong :premises (t10 t11)
  have t12 : π (T r (Eqv r P19 P17)) { refine cong_or t10 t11 };
  // t13 (cl (not (= @p_23 @p_21)) (not @p_23) @p_21) :rule equiv_pos2
  have t13 : π (T r (Eqv r P23 P21) ⇒ T r P23 ⇒ (P21 ⇒ r) ⇒ r)
    { refine equiv_pos2 };
  // t14 (cl (= @p_22 (A w))) :rule rare_rewrite bool-double-not-elim
  have t14 : π (T r (Eqv r ((A w ⇒ r) ⇒ r) (A w))) { refine double_not_elim };
  // t15 (cl (= @p_23 @p_21)) :rule cong :premises (t14)
  have t15 : π (T r (Eqv r P23 P21)) { refine cong_imp_r [r] [NA ⇒ r] t14 };
  // t16 (cl @p_23 @p_15) :rule implies_neg1
  have t16 : π ((P23 ⇒ r) ⇒ ((NA ⇒ r) ⇒ r) ⇒ r)
    { refine implies_neg1 [r] [NA ⇒ r] [(A w ⇒ r) ⇒ r] };
  // t17.t3 = t30 (cl (not (= EA @p_15)) (not EA) @p_15) :rule equiv_pos2
  have t30 : π (T r (Eqv r EA (NA ⇒ r)) ⇒ T r EA ⇒ ((NA ⇒ r) ⇒ r) ⇒ r)
    { refine equiv_pos2 };
  // t17.t4 = t31 (cl (= EA @p_15)) :rule connective_def
  have t31 : π (T r (Eqv r EA (NA ⇒ r))) { refine connective_def_ex A };
  // t17.t5 = t32 (cl @p_15) :rule resolution :premises (t30 t31 a1)
  have t32 : π (T r (NA ⇒ r)) { refine λ k, t30 t31 a1 k };
  // t17.t0 (cl (not (= @p_15 @p_22)) @p_18 @p_22) :rule equiv_pos2
  have t17_t0 : π (T r (Eqv r (NA ⇒ r) ((A w ⇒ r) ⇒ r)) ⇒ T r (NA ⇒ r)
                   ⇒ (((A w ⇒ r) ⇒ r) ⇒ r) ⇒ r) { refine equiv_pos2 };
  // t17.t1 (cl (= NA (not (A w)))) :rule sko_forall, with w for the ε-term
  have t17_t1 : π (T r (Eqv r NA (A w ⇒ r)))
    { refine sko_forall_witness A w aw };
  // t17.t2 (cl (= @p_15 @p_22)) :rule cong :premises (t17.t1)
  have t17_t2 : π (T r (Eqv r (NA ⇒ r) ((A w ⇒ r) ⇒ r)))
    { refine cong_not t17_t1 };
  // t17.t6 (cl @p_22) :rule resolution :premises (t17.t0 t17.t2 t17.t5)
  have t17_t6 : π (T r ((A w ⇒ r) ⇒ r)) { refine λ k, t17_t0 t17_t2 t32 k };
  // t17 (cl @p_18 @p_22) :rule subproof :discharge (t17.a0)
  have t17 : π (T r (NA ⇒ r) ⇒ (((A w ⇒ r) ⇒ r) ⇒ r) ⇒ r)
    { refine λ _, t17_t6 };
  // t18 (cl @p_23 @p_22) :rule resolution :premises (t16 t17)
  have t18 : π ((P23 ⇒ r) ⇒ (((A w ⇒ r) ⇒ r) ⇒ r) ⇒ r)
    { refine λ k k22, t16 k (λ v, t17 (λ u, u v) k22) };
  // t19 (cl @p_23 (not @p_22)) :rule implies_neg2
  have t19 : π ((P23 ⇒ r) ⇒ T r ((A w ⇒ r) ⇒ r) ⇒ r)
    { refine implies_neg2 [r] [NA ⇒ r] [(A w ⇒ r) ⇒ r] };
  // t20 (cl @p_23 @p_23) :rule resolution :premises (t18 t19)
  have t20 : π ((P23 ⇒ r) ⇒ (P23 ⇒ r) ⇒ r)
    { refine λ k k', t18 k (λ v, t19 k' (λ u, u v)) };
  // t21 (cl @p_23) :rule contraction
  have t21 : π (T r P23) { refine λ k, t20 k k };
  // t22 (cl @p_21) :rule resolution :premises (t13 t15 t21)
  have t22 : π (T r P21) { refine λ k, t13 t15 t21 k };
  // t23 (cl @p_18 (A w)) :rule implies :premises (t22)
  have t23 : π (T r (NA ⇒ r) ⇒ (A w ⇒ r) ⇒ r)
    { refine implies [r] [NA ⇒ r] [A w] t22 };
  // t24 (cl @p_19 (not @p_18)) :rule or_neg :args (0)
  have t24 : π ((P19 ⇒ r) ⇒ T r ((NA ⇒ r) ⇒ r) ⇒ r) { refine or_neg_0 };
  // t25 (cl @p_19 (not (A w))) :rule or_neg :args (1)
  have t25 : π ((P19 ⇒ r) ⇒ T r (A w) ⇒ r) { refine or_neg_1 };
  // t26 (cl @p_19 @p_19) :rule resolution :premises (t23 t24 t25)
  have t26 : π ((P19 ⇒ r) ⇒ (P19 ⇒ r) ⇒ r)
    { refine λ k k', t23 (λ v, t24 k (λ u, u v)) (λ y, t25 k' (λ u, u y)) };
  // t27 (cl @p_19) :rule contraction
  have t27 : π (T r P19) { refine λ k, t26 k k };
  // t28 (cl @p_17) :rule resolution :premises (t9 t12 t27)
  have t28 : π (T r P17) { refine λ k, t9 t12 t27 k };
  // t29 (cl NA (A w)) :rule or :premises (t28)
  have t29 : π ((NA ⇒ r) ⇒ (A w ⇒ r) ⇒ r) { refine or_ t28 };
  // t33 (cl (A w)) :rule resolution :premises (t29 t32)
  have t33 : π (T r (A w)) { refine λ k9, t32 (λ u, t29 u k9) };
  // t34 (cl (or (not Fo) @p_11)) :rule forall_inst :args (w)
  have t34 : π (T r ((Fo ⇒ r) ∨ P11))
    { refine forall_inst (λ x, (A x ⇒ r) ∨ B x) w };
  // t35 (cl (not Fo) @p_11) :rule or
  have t35 : π (T r Fo ⇒ (P11 ⇒ r) ⇒ r) { refine or_ t34 };
  // t36 (cl (not (= Fi Fo)) (not Fi) Fo) :rule equiv_pos2
  have t36 : π (T r (Eqv r Fi Fo) ⇒ T r Fi ⇒ (Fo ⇒ r) ⇒ r)
    { refine equiv_pos2 };
  // t37 (cl (= Fi Fo)) :rule bind, under x: bool-impl-elim
  have t37 : π (T r (Eqv r Fi Fo))
    { refine bind_forall (λ x, A x ⇒ T r (B x)) (λ x, (A x ⇒ r) ∨ B x)
                         (λ x, impl_elim) };
  // t38 (cl Fo) :rule resolution :premises (t36 t37 a0)
  have t38 : π (T r Fo) { refine λ k, t36 t37 a0 k };
  // t39 (cl @p_11) :rule resolution :premises (t35 t38)
  have t39 : π (T r P11) { refine t35 t38 };
  // t40 (cl (B w)) :rule resolution :premises (t8 t33 t39)
  have t40 : π (T r (B w)) { refine λ k5, t8 t33 k5 t39 };
  // t47 (cl) :rule resolution :premises (t6 t40 t46)
  refine t6 t46 t40
end;

opaque symbol ex_mono (A B : τ nat → Prop) :
  π (`∃ x, A x) → π (`∀ x, A x ⇒ B x) → π (`∃ x, B x) ≔
  λ hex himp,
    ∃ₑ hex (λ w aw,
      replay_ex_mono A B w aw (unit (λ x, unit (λ e, unit (himp x e))))
        (unit hex) goal);

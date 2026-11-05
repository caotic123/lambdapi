// Problems for constructionism_why3_test.ml. Every symbol whose type is
// Π x̄, π G is one problem: the test introduces x̄, as the why3 tactic does,
// and builds the Why3 task with Why3_tactic.translate_goal.
//
// Avoid ⊤ and ⊥: tests/OK/Prop.lp declares `builtin "bot" ≔ ⊤`, so ⊤ is
// sent as false and ⊥ becomes an ordinary atom.
require open tests.OK.Prop tests.OK.Set tests.OK.FOL;

constant symbol nat : Set;
constant symbol zero : τ nat;
constant symbol succ : τ nat → τ nat;
symbol even : τ nat → Prop;
symbol plus : τ nat → τ nat → τ nat;
rule plus zero $n ↪ $n;
symbol P : (τ nat → Prop) → Prop;

// Current set: the why3 goals of tests/why3_examples, as the tactic sees
// them (see tests/alethe/why3_examples/README.md).

// ex1_propositional.lp
symbol ex1 (p q : Prop) : π (p ⇒ q) → π p → π ((q ∧ p) ∨ ¬ p);
// ex2_first_order.lp
symbol ex2 (q : Prop) :
  π (even zero) → π (`∀ n, even n ⇒ even (succ (succ n))) →
  π (even (succ (succ zero)) ∧ (q ⇒ q));
// ex3_rewrite_rules.lp, after `simplify plus`
symbol ex3a : π (even zero) → π (even zero);
// ex3_rewrite_rules.lp, after `simplify two`
symbol ex3b :
  π (`∀ n, even n ⇒ even (succ (succ n))) → π (even zero) →
  π (even (succ (succ zero)));
// ex4_opaque_atoms.lp
symbol ex4 : π (P (λ x, even (plus zero x))) → π (P (λ x, even x));

// Extra problems, to exercise the fallback.

// Intuitionistic, and geometric once the goal is introduced.
symbol mt (p q : Prop) : π (p ⇒ q) → π (¬ q) → π (¬ p);
symbol curry (p q r : Prop) : π ((p ∧ q) ⇒ r) → π (p ⇒ q ⇒ r);
symbol all_mp (A B : τ nat → Prop) :
  π (`∀ x, A x ⇒ B x) → π (`∀ x, A x) → π (`∀ x, B x);
symbol ex_mono (A B : τ nat → Prop) :
  π (`∃ x, A x) → π (`∀ x, A x ⇒ B x) → π (`∃ x, B x);

// Intuitionistic, but not geometric: a hypothesis has ⇒, ¬ or ∀ in a
// negative position.
symbol imp_premise (p q r : Prop) : π ((p ⇒ q) ⇒ r) → π q → π r;
symbol triple_neg (p : Prop) : π (¬ ¬ ¬ p) → π (¬ p);
symbol all_premise (A : τ nat → Prop) (q : Prop) :
  π ((`∀ x, A x) ⇒ q) → π (`∀ x, A x) → π q;

// Classical only.
symbol em (p : Prop) : π (p ∨ ¬ p);
symbol dne (p : Prop) : π (¬ ¬ p) → π p;
symbol peirce (p q : Prop) : π (((p ⇒ q) ⇒ p) ⇒ p);
symbol contra (p q : Prop) : π (¬ q ⇒ ¬ p) → π (p ⇒ q);
symbol not_all (A : τ nat → Prop) : π (¬ (`∀ x, A x)) → π (`∃ x, ¬ A x);
symbol drinker (A : τ nat → Prop) : π (`∃ x, A x ⇒ `∀ y, A y);
// Double-negation shift: negative goal, but first-order.
symbol dns (A : τ nat → Prop) :
  π (`∀ x, ¬ ¬ A x) → π (¬ ¬ (`∀ x, A x));

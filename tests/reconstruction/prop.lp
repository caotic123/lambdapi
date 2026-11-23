// Propositional problems for the reconstruction pipeline
// (why3 → CVC5 → Carcara → Lambdapi). See README.md.
//
// Every atom is a variable of the goal, so every constant of the SMT-LIB
// problem is matched: the holes left are only the premises (one per
// hypothesis) and the goal (statement of the theorem → goal).
require open Stdlib.Set Stdlib.Prop Stdlib.FOL;
require alethe.core alethe.prop alethe.rare.prop;

prover "CVC5";
prover_timeout 10;

// Intuitionistic.

opaque symbol id (p : Prop) : π p → π p ≔
begin why3 end;

opaque symbol and_elim (p q : Prop) : π (p ∧ q) → π p ≔
begin why3 end;

opaque symbol or_intro (p q : Prop) : π p → π (p ∨ q) ≔
begin why3 end;

opaque symbol mp (p q : Prop) : π (p ⇒ q) → π p → π q ≔
begin why3 end;

opaque symbol ex1 (p q : Prop) : π (p ⇒ q) → π p → π ((q ∧ p) ∨ ¬ p) ≔
begin why3 end;

opaque symbol mt (p q : Prop) : π (p ⇒ q) → π (¬ q) → π (¬ p) ≔
begin why3 end;

opaque symbol curry (p q r : Prop) : π ((p ∧ q) ⇒ r) → π (p ⇒ q ⇒ r) ≔
begin why3 end;

opaque symbol imp_premise (p q r : Prop) : π ((p ⇒ q) ⇒ r) → π q → π r ≔
begin why3 end;

opaque symbol triple_neg (p : Prop) : π (¬ ¬ ¬ p) → π (¬ p) ≔
begin why3 end;

opaque symbol iff_elim (p q : Prop) : π (p ⇔ q) → π q → π p ≔
begin why3 end;

opaque symbol iff_trans (p q r : Prop) :
  π (p ⇔ q) → π (q ⇔ r) → π (p ⇔ r) ≔
begin why3 end;

opaque symbol syllogism (p q r : Prop) :
  π ((p ⇒ q) ⇒ (q ⇒ r) ⇒ (p ⇒ r)) ≔
begin why3 end;

opaque symbol and_comm (p q : Prop) : π (p ∧ q ⇒ q ∧ p) ≔
begin why3 end;

opaque symbol or_elim (p q r : Prop) :
  π (p ∨ q) → π (p ⇒ r) → π (q ⇒ r) → π r ≔
begin why3 end;

opaque symbol top_intro : π ⊤ ≔
begin why3 end;

opaque symbol bot_elim (p : Prop) : π ⊥ → π p ≔
begin why3 end;

// Carcara's Lambdapi backend has no rule not_equiv1 (2026-11-19): these two
// are translated with --admit-unsupported.
opaque symbol distrib (p q r : Prop) :
  π (p ∧ (q ∨ r) ⇔ (p ∧ q) ∨ (p ∧ r)) ≔
begin why3 end;

opaque symbol de_morgan (p q : Prop) : π (¬ (p ∨ q) ⇔ ¬ p ∧ ¬ q) ≔
begin why3 end;

// Classical only.

opaque symbol em (p : Prop) : π (p ∨ ¬ p) ≔
begin why3 end;

opaque symbol dne (p : Prop) : π (¬ ¬ p) → π p ≔
begin why3 end;

opaque symbol peirce (p q : Prop) : π (((p ⇒ q) ⇒ p) ⇒ p) ≔
begin why3 end;

opaque symbol contra (p q : Prop) : π (¬ q ⇒ ¬ p) → π (p ⇒ q) ≔
begin why3 end;

opaque symbol not_and (p q : Prop) : π (¬ (p ∧ q)) → π (¬ p ∨ ¬ q) ≔
begin why3 end;

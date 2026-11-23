// First-order problems for the reconstruction pipeline. See README.md.
//
// The sort nat and the symbols zero, succ, even are global symbols of this
// file. The tactic matches the constants of the SMT-LIB problem only with
// the variables of the goal, so each of them is a hole, and so is every
// variable whose type mentions nat (2026-11-19).
require open Stdlib.Set Stdlib.Prop Stdlib.FOL;
require alethe.core alethe.prop alethe.rare.prop alethe.quant;

prover "CVC5";
prover_timeout 10;

constant symbol nat : Set;
constant symbol zero : τ nat;
constant symbol succ : τ nat → τ nat;
symbol even : τ nat → Prop;

// Global symbols only.

opaque symbol ground : π (even zero) → π (even zero) ≔
begin why3 end;

opaque symbol ex3b :
  π (`∀ n, even n ⇒ even (succ (succ n))) → π (even zero) →
  π (even (succ (succ zero))) ≔
begin why3 end;

opaque symbol ex2 (q : Prop) :
  π (even zero) → π (`∀ n, even n ⇒ even (succ (succ n))) →
  π (even (succ (succ zero)) ∧ (q ⇒ q)) ≔
begin why3 end;

opaque symbol uf (A : τ nat → Prop) :
  π (`∀ x, A x ⇒ A (succ x)) → π (A zero) → π (A (succ (succ zero))) ≔
begin why3 end;

// Predicate variables over the global sort.

opaque symbol inst (A : τ nat → Prop) (c : τ nat) :
  π (`∀ x, A x) → π (A c) ≔
begin why3 end;

opaque symbol ex_intro (A : τ nat → Prop) (c : τ nat) :
  π (A c) → π (`∃ x, A x) ≔
begin why3 end;

opaque symbol all_mp (A B : τ nat → Prop) :
  π (`∀ x, A x ⇒ B x) → π (`∀ x, A x) → π (`∀ x, B x) ≔
begin why3 end;

opaque symbol ex_mono (A B : τ nat → Prop) :
  π (`∃ x, A x) → π (`∀ x, A x ⇒ B x) → π (`∃ x, B x) ≔
begin why3 end;

opaque symbol all_premise (A : τ nat → Prop) (q : Prop) :
  π ((`∀ x, A x) ⇒ q) → π (`∀ x, A x) → π q ≔
begin why3 end;

opaque symbol all_swap (R : τ nat → τ nat → Prop) :
  π (`∀ x, `∀ y, R x y) → π (`∀ y, `∀ x, R x y) ≔
begin why3 end;

// Classical only.

opaque symbol not_all (A : τ nat → Prop) :
  π (¬ (`∀ x, A x)) → π (`∃ x, ¬ A x) ≔
begin why3 end;

opaque symbol dns (A : τ nat → Prop) :
  π (`∀ x, ¬ ¬ A x) → π (¬ ¬ (`∀ x, A x)) ≔
begin why3 end;

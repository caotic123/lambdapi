// Fatal: valid, but CVC5 answers unknown (2026-11-19, CVC5 1.3.4-dev). After
// skolemization the hypotheses are ∀y. R a y and ∀x. ¬ R x b: no ground R
// term triggers E-matching. CVC5 proves it with --enum-inst, which the why3
// tactic does not pass. Expected error: "CVC5" did not find a proof.
require open Stdlib.Set Stdlib.Prop Stdlib.FOL;
require alethe.core alethe.prop alethe.rare.prop alethe.quant;

prover "CVC5";
prover_timeout 10;

constant symbol nat : Set;

opaque symbol ex_all (R : τ nat → τ nat → Prop) :
  π (`∃ x, `∀ y, R x y) → π (`∀ y, `∃ x, R x y) ≔
begin why3 end;

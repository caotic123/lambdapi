// Crash in Why3's SMT-LIB printer (2026-11-19). The variable a : Set
// becomes a Why3 type variable, and the task has no `use BuiltIn`, so
// printing raises "This declaration isn't supported: predicate (=) 'a 'a.
// smt: polymorphism must be encoded". See "Polymorphic tasks crash" in
// AGENTS.md: the fix is to declare a as an abstract type.
require open Stdlib.Set Stdlib.Prop Stdlib.FOL;
require alethe.core alethe.prop alethe.rare.prop alethe.quant;

prover "CVC5";
prover_timeout 10;

opaque symbol poly (a : Set) (p : τ a → Prop) :
  π (¬ (`∃ x : τ a, p x) ⇔ (`∀ x, ¬ (p x))) ≔
begin why3 end;

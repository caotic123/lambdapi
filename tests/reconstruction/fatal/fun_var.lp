// Crash in the why3 tactic, before CVC5 is called (2026-11-19). The
// variable f : τ nat → τ nat is neither a sort, an object, a hypothesis nor
// a predicate, so translate_goal drops it; then f x reaches
// `| None -> assert false` in translate_term (src/handle/why3_tactic.ml).
// The same problem with a global function symbol is fol.lp's uf.
require open Stdlib.Set Stdlib.Prop Stdlib.FOL;
require alethe.core alethe.prop alethe.rare.prop alethe.quant;

prover "CVC5";
prover_timeout 10;

constant symbol nat : Set;

opaque symbol fun_var (f : τ nat → τ nat) (A : τ nat → Prop) (c : τ nat) :
  π (`∀ x, A x ⇒ A (f x)) → π (A c) → π (A (f (f c))) ≔
begin why3 end;

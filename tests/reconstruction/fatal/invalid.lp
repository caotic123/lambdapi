// Fatal: the goal is not valid, so CVC5 answers sat and there is no proof
// to reconstruct. Expected error: "CVC5" did not find a proof.
require open Stdlib.Set Stdlib.Prop Stdlib.FOL;
require alethe.core alethe.prop alethe.rare.prop;

prover "CVC5";
prover_timeout 10;

opaque symbol invalid (p q : Prop) : π (p ⇒ q) ≔
begin why3 end;

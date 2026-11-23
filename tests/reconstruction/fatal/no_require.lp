// Fatal: the translation uses modules of Carcara's library that this file
// does not require, and the tactic does not load them behind the user's
// back. Expected error: "Add to the file: require alethe.core alethe.prop
// alethe.rare.prop;".
require open Stdlib.Set Stdlib.Prop Stdlib.FOL;

prover "CVC5";
prover_timeout 10;

opaque symbol mp (p q : Prop) : π (p ⇒ q) → π p → π q ≔
begin why3 end;

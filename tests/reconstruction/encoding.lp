// A goal stated in the encoding of tests.OK instead of the Stdlib. See
// README.md.
//
// The translation is in the encoding of Carcara's library (over the
// Stdlib), so it is loaded and its theorem applied, but its code cannot be
// put in this file: the builtins are other symbols, and the constants p and
// q (of type τ o) have no counterpart among the variables (of type
// tests.OK.Prop.Prop).
//
// The modules of Carcara's library must be required before tests.OK is
// opened: requiring them afterwards makes the builtin "Prf" the π of the
// Stdlib, and the tactic then fails before calling CVC5 ("The goal is not of
// the form [Stdlib.Prop.π _]").
require alethe.core alethe.prop alethe.rare.prop;
require open tests.OK.Prop tests.OK.Set tests.OK.FOL;

prover "CVC5";
prover_timeout 10;

opaque symbol mp (p q : Prop) : π (p ⇒ q) → π p → π q ≔
begin why3 end;

(** Checking that a rule preserves typing (subject reduction property). *)

open Core open Term
open Common

(** [check_rule r] checks whether the pre-rule [r] is well-typed in
   signature state [ss] and then construct the corresponding rule. Note that
   [Fatal] is raised in case of error. *)
val check_rule : Pos.popt -> sym_rule -> sym_rule

(** [check_constraint pos cr] checks that the typed constraint [cr] (the [when]
    construct) is type-correct: its guard type is typable and the two sides of
    every equation have the same type. [Fatal] is raised on error. *)
val check_constraint : Pos.popt -> constr_rule -> constr_rule

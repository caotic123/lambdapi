(** Calling a prover using Why3. *)

open Common
open Core
open Timed

type output_solver =
  | Proof of string (** Valid, with a complete proof (Alethe for CVC5). *)
  | Invalid of string (** No proof found. *)
  | Holey
  (** Valid, but without a complete proof: no proof was asked for, or the
      proof could not be read, or it has steps justified by "hole". *)

(** [default_prover] contains the name of the current prover. Note that it can
    be changed by using the "set prover <string>" command. *)
val default_prover : string ref

(** [timeout] is the current time limit (in seconds) for a Why3 prover to find
    a proof. It can be changed with "set prover <int>". *)
val timeout : int ref

(** [smt_proofs] tells whether provers are asked for a proof (experimental,
    only CVC5 for now). It is set by "lambdapi check
    --experimental-smt-proofs". *)
val smt_proofs : bool ref

(** [handle ss pos ps prover_name gt] runs the Why3 prover corresponding to
    [prover_name] (if given or a default one otherwise) on the goal type [gt],
    and fails if no proof is found. *)
val handle: Sig_state.t -> Pos.popt -> string option -> Goal.goal_typ -> output_solver

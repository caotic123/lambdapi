(** Calling a prover using Why3. *)

open Common
open Core
open Timed

(** How Lambdapi symbols, variables and terms are mapped to Why3 symbols or
    variables. *)
type l2y =
  { s2ts : (Term.sym * Why3.Ty.tysymbol) list
  (** Mapping of type symbols. *)
  ; t2ts : (Term.term * Why3.Ty.tysymbol) list
  (** Mapping of non-Why3 subtypes. *)
  ; v2tv : (Term.var * Why3.Ty.tvsymbol) list
  (** Mapping of type variables. *)
  ; s2ls : (Term.sym * (Why3.Term.lsymbol * bool)) list
  (** Mapping of function symbols. [true] is for predicates. *)
  ; v2ls : (Term.var * (Why3.Term.lsymbol * bool)) list
  (** Mapping of environment variables. [true] is for predicates. *)
  ; t2ls : (Term.term * Why3.Term.lsymbol) list
  (** Mapping of non-Why3 subterms. *)
  ; v2vs : (Term.var * Why3.Term.vsymbol) list
  (** Mapping of object variables. *) }

(** Result of a prover call. *)
type output_solver =
  | Proof of
      { problem : string; output : string
      ; l2y : l2y; hyps : (string * Why3.Term.term) list }
  (** Valid, with a proof: [problem] is the SMT-LIB problem sent to the
      prover, and [output] is what the prover printed ("unsat" and an
      Alethe proof for CVC5). [l2y] maps the symbols and variables of the
      goal to Why3, and [hyps] are the translated hypotheses, with their
      names, in the order of the task. *)
  | Invalid of string (** No proof found, by the prover of that name. *)
  | Holey (** Valid, but no proof was asked for. *)

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

(** [handle ss pos prover_name gt] runs the Why3 prover corresponding to
    [prover_name] (if given or a default one otherwise) on the goal type
    [gt]. *)
val handle :
  Sig_state.t -> Pos.popt -> string option -> Goal.goal_typ -> output_solver

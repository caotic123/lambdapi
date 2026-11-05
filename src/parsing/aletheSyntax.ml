(** Abstract syntax of Alethe proofs. *)

(** Constants, as written in the proof except for strings. Numerals have sort
    Int, decimals and rationals have sort Real. *)
type constant =
  | Numeral of string (** [12] or [-12] *)
  | Decimal of string (** [1.5] or [-1.5] *)
  | Rational of string (** [1/2] or [-1/2] *)
  | Hexadecimal of string (** [#x1F] *)
  | Binary of string (** [#b101] *)
  | String of string (** Contents, without quotes and with [""] unescaped. *)

(** S-expressions, used as attribute values. *)
type s_expr =
  | SSymbol of string
  | SConst of constant
  | SKeyword of string (** [:k], stored without the colon. *)
  | SList of s_expr list

(** SMT-LIB attribute [:k] or [:k v], stored without the colon. *)
type attribute = string * s_expr option

type term =
  | Symbol of string
  | Const of constant
  | App of string * term list
  | Annot of term * attribute list (** [(! t :named n)] *)
  | Forall of sorted_var list * term (** [(forall ((x1 S1) ... ) t)] *)
  | Exists of sorted_var list * term (** [(exists ((x1 S1) ... ) t)] *)
  | Choice of sorted_var * term (** [(choice ((x S)) t)] *)
  | Let of (string * term) list * term (** [(let ((x1 t1) ... ) t)] *)

(** Sorted variable [(x S)]. Sorts are parsed as terms, e.g. [Int] or
    [(Array Int Int)]. *)
and sorted_var = string * term

(** Element of the context of an anchor. *)
type context_assignment =
  | Var of sorted_var (** [(x S)] *)
  | Assign of sorted_var * term (** [(:= (x S) t)] *)

type command =
  | Assume of string * term * attribute list
  (** [(assume h t attrs)] *)
  | Step of
      { id : string
      ; clause : term list
      ; rule : string
      ; premises : string list
      ; args : term list
      ; attributes : attribute list }
  (** [(step id (cl t1 ... tn) :rule r :premises (p1 ... pk) :args
      (a1 ... am) attrs)], where [:premises] and [:args] are optional. *)
  | Anchor of string * context_assignment list * attribute list
  (** [(anchor :step id :args (c1 ... cn) attrs)], where [:args] is
      optional. *)
  | DefineFun of string * sorted_var list * term * term
  (** [(define-fun f ((x1 S1) ... (xn Sn)) S t)] *)

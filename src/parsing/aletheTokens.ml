(** Tokens of the Alethe proof format, produced by [AletheLexer]. *)

type token =
  | STEP
  | CLAUSE
  | COLON
  | ASSIGN
  | RULE
  | PREMISES
  | ARGS
  | ANCHOR
  | ASSUME
  | DEFINEFUN
  | FORALL
  | EXISTS
  | CHOICE
  | LET
  | BANG
  | RATIONAL of string
  | NEGDECIMAL of string
  | NEGNUMERAL of string
  | DECIMAL of string
  | NUMERAL of string
  | HEXADECIMAL of string
  | BINARY of string
  | STRING of string (** Contents, without quotes and with [""] unescaped. *)
  | LEFTPAR
  | RIGHTPAR
  | SYMBOL of string
  | EOF
  
(** [pp_token ppf t] prints the token [t] on [ppf], for debugging. *)
let pp_token : Format.formatter -> token -> unit = fun ppf t ->
  match t with
  | STEP -> Format.pp_print_string ppf "STEP"
  | CLAUSE -> Format.pp_print_string ppf "CLAUSE"
  | COLON -> Format.pp_print_string ppf "COLON"
  | ASSIGN -> Format.pp_print_string ppf "ASSIGN"
  | RULE -> Format.pp_print_string ppf "RULE"
  | PREMISES -> Format.pp_print_string ppf "PREMISES"
  | ARGS -> Format.pp_print_string ppf "ARGS"
  | ANCHOR -> Format.pp_print_string ppf "ANCHOR"
  | ASSUME -> Format.pp_print_string ppf "ASSUME"
  | DEFINEFUN -> Format.pp_print_string ppf "DEFINEFUN"
  | FORALL -> Format.pp_print_string ppf "FORALL"
  | EXISTS -> Format.pp_print_string ppf "EXISTS"
  | CHOICE -> Format.pp_print_string ppf "CHOICE"
  | LET -> Format.pp_print_string ppf "LET"
  | BANG -> Format.pp_print_string ppf "BANG"
  | RATIONAL s -> Format.fprintf ppf "RATIONAL %s" s
  | NEGDECIMAL s -> Format.fprintf ppf "NEGDECIMAL %s" s
  | NEGNUMERAL s -> Format.fprintf ppf "NEGNUMERAL %s" s
  | DECIMAL s -> Format.fprintf ppf "DECIMAL %s" s
  | NUMERAL s -> Format.fprintf ppf "NUMERAL %s" s
  | HEXADECIMAL s -> Format.fprintf ppf "HEXADECIMAL %s" s
  | BINARY s -> Format.fprintf ppf "BINARY %s" s
  | STRING s -> Format.fprintf ppf "STRING %S" s
  | LEFTPAR -> Format.pp_print_string ppf "LEFTPAR"
  | RIGHTPAR -> Format.pp_print_string ppf "RIGHTPAR"
  | SYMBOL s -> Format.fprintf ppf "SYMBOL %s" s
  | EOF -> Format.pp_print_string ppf "EOF"

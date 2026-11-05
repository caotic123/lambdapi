{
  (** Dedukti source file parsing/lexer.mll. *)

  open Lexing
  open Format
  open Common
  open AletheTokens

  let get_loc lexbuf = lexbuf.lex_start_p, lexbuf.lex_curr_p
  let fail lps msg = Error.fatal (Some (Pos.locate lps)) "%s" msg

  (** [unescape s] replaces every two consecutive double quotes by one in the
      contents [s] of an SMT-LIB string literal. *)
  let unescape s =
    let b = Buffer.create (String.length s) in
    let i = ref 0 in
    while !i < String.length s do
      Buffer.add_char b s.[!i];
      i := !i + (if s.[!i] = '"' then 2 else 1)
    done;
    Buffer.contents b
}

let space   = [' ' '\t' '\r']
let mident = ['a'-'z' 'A'-'Z' '0'-'9' '_']+
let ident   = ['a'-'z' 'A'-'Z' '0'-'9' '_' '!' '?']['a'-'z' 'A'-'Z' '0'-'9' '_' '!' '?' '\'' ]*

(* SMT-LIB symbols: a simple symbol does not start with a digit. *)
let sym_start = ['a'-'z' 'A'-'Z' '~' '!' '@' '$' '%' '^' '&' '*' '_' '-' '+'
                 '=' '<' '>' '.' '?' '/']
let simple_symbol = sym_start (sym_start | ['0'-'9'])*
let quoted_symbol = '|' [^ '|' '\\']* '|'

(* SMT-LIB constants. Inside a string, a double quote is written [""]. *)
let numeral = '0' | ['1'-'9'] ['0'-'9']*
let positive_numeral = ['1'-'9'] ['0'-'9']*
let decimal = numeral '.' '0'* numeral
let hexadecimal = "#x" ['0'-'9' 'a'-'f' 'A'-'F']+
let binary = "#b" ['0' '1']+
let string_contents = ([^ '"'] | "\"\"")*


rule token = parse
  | "step"  {STEP}
  | "cl" {CLAUSE}
  | ':' {COLON}
  | ":=" {ASSIGN}
  | "rule" {RULE}
  | "premises" {PREMISES}
  | "args" {ARGS}
  | "anchor" {ANCHOR}
  | "assume" {ASSUME}
  | "define-fun" {DEFINEFUN}
  | "forall" {FORALL}
  | "exists" {EXISTS}
  | "choice" {CHOICE}
  | "let" {LET}
  | "!" {BANG}
  | '-'? numeral '/' positive_numeral as s {RATIONAL s}
  | '-' decimal as s {NEGDECIMAL s}
  | '-' numeral as s {NEGNUMERAL s}
  | decimal as s {DECIMAL s}
  | numeral as s {NUMERAL s}
  | hexadecimal as s {HEXADECIMAL s}
  | binary as s {BINARY s}
  | '"' (string_contents as s) '"' {STRING (unescape s)}
  | space       { token lexbuf  }
  | '\n'        { new_line lexbuf ; token lexbuf }
  | '('         { LEFTPAR       }
  | ')'         { RIGHTPAR      }
  | simple_symbol as s { SYMBOL s }
  | quoted_symbol as s { SYMBOL s }
  | eof { EOF }
  | _   as c
  { let msg = sprintf "Unexpected character '%c'." c in
    fail (get_loc lexbuf) msg }

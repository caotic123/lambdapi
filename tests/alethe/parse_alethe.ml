(** [parse_alethe [file]] prints, one per line, the commands parsed by
    [Parsing.Parser.Alethe] from [file] (or the standard input), until the
    end of the input or a parse error. *)

open Common
open Parsing
open AletheSyntax

let list f xs = "[" ^ String.concat "; " (List.map f xs) ^ "]"

let constant = function
  | Numeral s -> "Numeral " ^ s
  | Decimal s -> "Decimal " ^ s
  | Rational s -> "Rational " ^ s
  | Hexadecimal s -> "Hexadecimal " ^ s
  | Binary s -> "Binary " ^ s
  | String s -> Printf.sprintf "String %S" s

let rec s_expr = function
  | SSymbol s -> s
  | SConst c -> "{" ^ constant c ^ "}"
  | SKeyword k -> ":" ^ k
  | SList es -> "(" ^ String.concat " " (List.map s_expr es) ^ ")"

let attribute (k, v) =
  ":" ^ k ^ match v with None -> "" | Some v -> " " ^ s_expr v

let rec term = function
  | Symbol s -> s
  | Const c -> "{" ^ constant c ^ "}"
  | App(f, ts) -> "(" ^ String.concat " " (f :: List.map term ts) ^ ")"
  | Annot(t, attrs) -> "Annot(" ^ term t ^ ", " ^ list attribute attrs ^ ")"
  | Forall(xs, t) -> "Forall(" ^ list sorted_var xs ^ ", " ^ term t ^ ")"
  | Exists(xs, t) -> "Exists(" ^ list sorted_var xs ^ ", " ^ term t ^ ")"
  | Choice(x, t) -> "Choice(" ^ sorted_var x ^ ", " ^ term t ^ ")"
  | Let(bs, t) -> "Let(" ^ list sorted_var bs ^ ", " ^ term t ^ ")"

and sorted_var (x, s) = "(" ^ x ^ " " ^ term s ^ ")"

let context_assignment = function
  | Var x -> "Var " ^ sorted_var x
  | Assign(x, t) -> "Assign(" ^ sorted_var x ^ ", " ^ term t ^ ")"

let command = function
  | Assume(h, t, attrs) ->
      Printf.sprintf "Assume(%s, %s, %s)" h (term t) (list attribute attrs)
  | Step s ->
      Printf.sprintf
        "Step{id=%s; clause=%s; rule=%s; premises=%s; args=%s; attributes=%s}"
        s.id (list term s.clause) s.rule (list Fun.id s.premises)
        (list term s.args) (list attribute s.attributes)
  | Anchor(id, ctx, attrs) ->
      Printf.sprintf "Anchor(%s, %s, %s)" id (list context_assignment ctx)
        (list attribute attrs)
  | DefineFun(f, xs, s, t) ->
      Printf.sprintf "DefineFun(%s, %s, %s, %s)" f (list sorted_var xs)
        (term s) (term t)

let () =
  let fname, ic =
    match Sys.argv with
    | [|_|] -> "<stdin>", stdin
    | [|_; f|] -> f, open_in f
    | _ -> prerr_endline "usage: parse_alethe [file]"; exit 2
  in
  try
    Stream.iter (fun (c : command Pos.loc) -> print_endline (command c.elt))
      (Parser.Alethe.parse_in_channel fname ic)
  with Error.Fatal(pos, msg, _) ->
    Format.printf "%a: error: %s@." Pos.pp (Option.join pos) msg;
    exit 1

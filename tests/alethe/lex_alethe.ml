(** [lex_alethe [file]] prints, one per line, the tokens read by
    [Parsing.AletheLexer.token] from [file] (or the standard input), with
    their position, until [EOF] or a lexing error. *)

open Common
open Parsing

let () =
  let fname, ic =
    match Sys.argv with
    | [|_|] -> "<stdin>", stdin
    | [|_; f|] -> f, open_in f
    | _ -> prerr_endline "usage: lex_alethe [file]"; exit 2
  in
  let lb = Lexing.from_channel ic in
  Lexing.set_filename lb fname;
  let rec loop () =
    let t = AletheLexer.token lb in
    let pos = Pos.locate (lb.lex_start_p, lb.lex_curr_p) in
    Format.printf "%s: %a@." (Pos.to_string pos) AletheTokens.pp_token t;
    if t <> AletheTokens.EOF then loop ()
  in
  try loop () with Error.Fatal(pos, msg, _) ->
    Format.printf "%a: error: %s@." Pos.pp (Option.join pos) msg;
    exit 1

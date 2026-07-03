(* The `when` typed-constraint firing pipeline.  A guard over the subject's TYPE,
   [path $a $x $y], with one equation [bnd $p = $x] (subject = slot 3).  Firing on
   a subject [p : path A X Y] must merge  [bnd p ≡ X]  in the e-graph.
   Heads (path, bnd) are free vars so we needn't fabricate symbols. *)
open Core.Term
open Egraph

let app f a = mk_Appl (f, a)
let patt i nm = mk_Patt (Some i, nm, [||])

let () =
  let g = create () in
  let path = mk_Vari (new_var "path") and bnd = mk_Vari (new_var "bnd") in
  let a = mk_Vari (new_var "A") and x = mk_Vari (new_var "X")
  and y = mk_Vari (new_var "Y") and p = mk_Vari (new_var "p") in

  (* when (p : path $a $x $y) ⊢ bnd $p ≡ $x      (subject = pattern slot 3) *)
  let cr =
    { cr_name    = "bdry"
    ; cr_type    = app (app (app path (patt 0 "a")) (patt 1 "x")) (patt 2 "y")
    ; cr_eqns    = [ (app bnd (patt 3 "p"), patt 1 "x") ]
    ; cr_subj    = 3
    ; cr_names   = [| "a"; "x"; "y"; "p" |]
    ; cr_vars_nb = 4
    ; cr_pos     = None } in

  let ty = app (app (app path a) x) y in        (* subject's type: path A X Y *)

  (* before firing:  bnd p  ≢  X *)
  assert (not (equiv g (intern g [] (app bnd p)) (intern g [] x)));

  assert (fire g [] cr ~subj:p ~ty);
  rebuild g;
  assert (equiv g (intern g [] (app bnd p)) (intern g [] x));   (* merge landed *)
  let q = mk_Vari (new_var "q") in
  assert (not (equiv g (intern g [] (app bnd q)) (intern g [] x)));  (* only p *)
  Printf.printf "fire ok: guard matched ⟹ merged bnd(p) ≡ X (and only p)\n";

  (* a non-matching type does not fire *)
  assert (not (fire g [] cr ~subj:p ~ty:(mk_Vari (new_var "Nope"))));
  Printf.printf "fire ok: non-matching type does not fire\n";

  (* fire_all over a list runs the whole pipeline *)
  fire_all g [] [ cr ] ~subj:p ~ty;
  rebuild g;
  Printf.printf "fire_all ok\n";

  print_endline "ALL CONSTRAINT TESTS PASSED"

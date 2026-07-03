(* PROBE (diagnostic): is [Repr.of_term]'s skolemization position-INDEPENDENT?
   i.e. does the SAME closed subterm intern identically regardless of how deep
   under binders it sits?  Congruence needs this: a node merged in one place must
   be recognised as the same node wherever it reappears. *)
open Core.Term
open Egraph

let idfn () =                        (* λ(_:Type). x                        *)
  let x = new_var "x" in
  mk_Abst (mk_Type, bind_var x (mk_Vari x))

let under_one () =                   (* λ(_:Type). (λ(_:Type). x)  — id nested 1 deep *)
  let z = new_var "z" in
  mk_Abst (mk_Type, bind_var z (idfn ()))

let () =
  let g = create () in
  (* Merge the STANDALONE identity (depth 0) with a marker free var M. *)
  let m   = mk_Vari (new_var "M") in
  let id0 = intern g [] (idfn ()) in
  let idM = intern g [] m in
  merge g id0 idM; rebuild g;

  (* Ask: is  λz.(λx.x)  ≡  λz.M  ?   True iff the NESTED λx.x interns the same as
     the standalone one (so congruence sees nested-id ≡ M ≡ standalone-id).  With de
     Bruijn INDICES both are #0, so it holds — this is the regression guard against
     the position-dependence that de Bruijn LEVELS used to exhibit. *)
  let z = new_var "z" in
  let lz_id = intern g [] (under_one ()) in
  let lz_M  = intern g [] (mk_Abst (mk_Type, bind_var z m)) in
  assert (equiv g lz_id lz_M);
  Printf.printf
    "binder ok: nested λx.x ≡ standalone λx.x (position-independent, index-keyed)\n";
  print_endline "ALL BINDER TESTS PASSED"

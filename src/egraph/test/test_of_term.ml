(* Exercise [Egraph.intern] / [Repr.of_term] on REAL Lambdapi [Term] values:
   the binder descent and de Bruijn-LEVEL skolemization (α-equivalence), plus
   [relate_type] through real terms. *)
open Core.Term
open Egraph

(* λ(_:Type). <name>   — the identity, bound var named [name]. *)
let idfn name =
  let x = new_var name in
  mk_Abst (mk_Type, bind_var x (mk_Vari x))

(* λ(_:Type).λ(_:Type). (first ? outer : inner)  — K when [fst], K* otherwise. *)
let proj n1 n2 ~fst =
  let x = new_var n1 and y = new_var n2 in
  let body = mk_Vari (if fst then x else y) in
  mk_Abst (mk_Type, bind_var x (mk_Abst (mk_Type, bind_var y body)))

let () =
  let g = create () in

  (* α-equivalence: λx.x ≡ λy.y  (the skolem is the de Bruijn LEVEL, not the name) *)
  let i1 = intern g [] (idfn "x") and i2 = intern g [] (idfn "y") in
  assert (equiv g i1 i2);

  (* K = λx.λy.x  ≠  K* = λx.λy.y *)
  let k  = intern g [] (proj "x" "y" ~fst:true)  in
  let ks = intern g [] (proj "x" "y" ~fst:false) in
  assert (not (equiv g k ks));

  (* α-equivalent K: λa.λb.a ≡ λx.λy.x *)
  let k' = intern g [] (proj "a" "b" ~fst:true) in
  assert (equiv g k k');
  Printf.printf
    "of_term ok: λx.x≡λy.y ; λx.λy.x≢λx.λy.y ; λx.λy.x≡λa.λb.a\n";

  (* typing relation on real terms: type(λz.z) = K.  Since λx.x ≡ λz.z, querying
     type(λx.x) lands in K's class too — relation + α-canonicity together. *)
  relate_type g [] (idfn "z") (proj "p" "q" ~fst:true);
  rebuild g;
  let ty_of_id = add g (type_of_repr (Repr.of_term Repr.empty_env (idfn "x"))) in
  assert (equiv g ty_of_id k);
  Printf.printf "relate_type ok: type(λx.x) ≡ K, shared across α-equal identities\n";

  (* normalization-before-insert: the β-redex (λf.f) a must collapse to a *)
  let a = mk_Vari (new_var "a") in
  assert (equiv g (intern g [] (mk_Appl (idfn "f", a))) (intern g [] a));
  Printf.printf "normalize ok: (λf.f) a ≡ a (β-reduced before insert)\n";

  print_endline "ALL OF_TERM TESTS PASSED"

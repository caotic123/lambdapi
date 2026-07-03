(* Test the e-graph: typing as the in-graph relation  type(x) = T,  and that
   the e-graph's congruence closure propagates it on its own:
       a ≡ b   ⟹   type(a) ≡ type(b)   ⟹   A ≡ B.
   We build [Repr.t] nodes directly (no parser / Term needed). *)
open Egraph

let sym s = Repr.(Mk (SSym s))
let type_node s = type_of_repr (sym s)

let () =
  let g = create () in
  let a  = add g (sym "a") and b  = add g (sym "b") in
  let ta = add g (sym "A") and tb = add g (sym "B") in
  (* typing facts as in-graph equations:  type(a) = A,  type(b) = B *)
  merge g (add g (type_node "a")) ta;
  merge g (add g (type_node "b")) tb;
  rebuild g;
  assert (equiv g (add g (type_node "a")) ta);   (* type(a) ≡ A *)
  assert (equiv g (add g (type_node "b")) tb);    (* type(b) ≡ B *)
  assert (not (equiv g ta tb));                   (* A ≢ B (nothing forces it) *)
  assert (not (equiv g a b));                     (* a ≢ b *)
  Printf.printf "step 1 ok: type(a)≡A, type(b)≡B, A≢B, a≢b\n";

  (* now identify the two terms:  a ≡ b *)
  merge g a b;
  rebuild g;
  assert (equiv g a b);
  assert (equiv g (add g (type_node "a")) (add g (type_node "b")));  (* congruence *)
  assert (equiv g ta tb);   (* ⟹ A ≡ B, decided purely by the e-graph *)
  Printf.printf
    "step 2 ok: a≡b ⟹ type(a)≡type(b) ⟹ A≡B (congruence closure)\n";

  print_endline "ALL EGRAPH TESTS PASSED"

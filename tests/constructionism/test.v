(* What does Sniper (CPP 2023, Blot et al., Section 4.2.2) do with the
   inductive predicate Inv_elt_list when its Boolean equivalent is not
   registered in Trakt?

   Run (opam switch `sniper`: Rocq 9.1.0, rocq-elpi 3.5.1, Sniper main
   97d5296, SMTCoq and Trakt dev, veriT9f48a98 in PATH), tested 2026-11-10:

     opam exec --switch=sniper -- rocq compile test.v

   Results, recorded below with `Fail`:
   - Without `Trakt Add Relation`, snipe fails on every goal containing
     Inv_elt_list, even `Inv_elt_list y l -> Inv_elt_list y l`, with
     "Verit.tactic: can only deal with equality over bool". Neither scope nor
     SMTCoq gives the solver the constructors or the inversion of the
     predicate, and SMTCoq rejects any atom in Prop (same error for
     `forall P : Prop, P -> P`) before veriT is called.
   - With the relation, Trakt (inside SMTCoq's verit) replaces Inv_elt_list
     by Inv_elt_list_bool _ _ = true. But scope runs before that, so it never
     sees Inv_elt_list_bool and states no equation for it: veriT answers
     `unknown` unless the goal mentions Inv_elt_list_bool (P1 needs none).
     Running Trakt before snipe (`revert_all; trakt Z bool; snipe`), which
     is the order described in the paper, proves all four goals.

   Notes:
   - Every type of the problem needs a CompDec instance. scope leaves the
     goal `CompDec elt_list` open otherwise, and verit fails on it with the
     same "equality over bool" error. As in Sniper's examples, it is a
     section variable here.
   - With SMTCoq loaded, `[|` and `|]` are single tokens (array notation):
     write `[ | a b]` and `[t | ]`. *)

From Sniper Require Import Sniper.
From Stdlib Require Import ZArith.
Local Open Scope Z_scope.
Set Default Proof Mode "Classic".

Inductive elt_list :=
| Nil : elt_list
| Cons : Z -> Z -> elt_list -> elt_list.

Inductive Inv_elt_list : Z -> elt_list -> Prop :=
| invNil : forall b, Inv_elt_list b Nil
| invCons : forall (a b j : Z) (q : elt_list),
    j <= a -> a <= b -> Inv_elt_list (b + 2) q ->
    Inv_elt_list j (Cons a b q).

Fixpoint Inv_elt_list_bool (j : Z) (l : elt_list) : bool :=
  match l with
  | Nil => true
  | Cons a b q => (j <=? a) && (a <=? b) && Inv_elt_list_bool (b + 2) q
  end.

(* ------------------------------------------------------------------ *)
(* Part 1: Inv_elt_list_decidable is not declared to Trakt.            *)

Section Without.
Variable HE : CompDec elt_list.

(* Controls: Z arithmetic and elt_list alone are fine. *)
Goal forall x y : Z, x <= y -> x <= y + 1.
Proof. snipe. Qed.

Goal forall (a b : Z) (l : elt_list), Cons a b l <> Nil.
Proof. snipe. Qed.

(* Control: any atom in Prop is rejected. *)
Goal forall P : Prop, P -> P.
Proof. Fail snipe. Abort.

(* P1: propositional, Inv_elt_list is only an atom. *)
Goal forall y l, Inv_elt_list y l -> Inv_elt_list y l.
Proof. Fail snipe. Abort.

(* P2: needs the constructor invNil. *)
Goal Inv_elt_list 0 Nil.
Proof. Fail snipe. Abort.

(* P3: needs inversion: [1, 0] is an empty interval. *)
Goal forall y, ~ Inv_elt_list y (Cons 1 0 Nil).
Proof. Fail snipe. Abort.

(* P4: Example 4.5 of the paper. *)
Lemma inv_elt_list_monoton : forall l y z,
  Inv_elt_list y l -> z <= y -> Inv_elt_list z l.
Proof.
  Fail induction l; snipe.
  Fail induction l; revert_all; trakt Z bool; snipe.
Abort.

End Without.

(* ------------------------------------------------------------------ *)
(* Part 2: the Boolean equivalent, registered with Trakt.              *)

Lemma Inv_elt_list_decidable : forall b e,
  Inv_elt_list b e <-> Inv_elt_list_bool b e = true.
Proof.
  intros b e; revert b; induction e as [ | a c q IH]; intro j; simpl; split.
  - reflexivity.
  - intros _; constructor.
  - intro H; inversion H; subst.
    apply andb_true_intro; split; [apply andb_true_intro; split | ].
    + apply Z.leb_le; assumption.
    + apply Z.leb_le; assumption.
    + apply IH; assumption.
  - intro H; apply andb_prop in H as [H1 H2]; apply andb_prop in H1 as [H0 H1].
    constructor; [apply Z.leb_le; assumption | apply Z.leb_le; assumption | ].
    apply IH; assumption.
Qed.

Trakt Add Relation 2 Inv_elt_list Inv_elt_list_bool Inv_elt_list_decidable.

Section With.
Variable HE : CompDec elt_list.

Goal forall y l, Inv_elt_list y l -> Inv_elt_list y l.
Proof. snipe. Qed.

(* veriT returns 'unknown': no equation for Inv_elt_list_bool. *)
Goal Inv_elt_list 0 Nil.
Proof.
  Fail snipe.
  Fail snipe Inv_elt_list_bool.
  revert_all; trakt Z bool; snipe.
Qed.

Goal forall y, ~ Inv_elt_list y (Cons 1 0 Nil).
Proof.
  Fail snipe.
  revert_all; trakt Z bool; snipe.
Qed.

Lemma inv_elt_list_monoton : forall l y z,
  Inv_elt_list y l -> z <= y -> Inv_elt_list z l.
Proof.
  Fail induction l; snipe.
  induction l; revert_all; trakt Z bool; snipe.
Qed.

End With.

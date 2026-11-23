require open alethe.core alethe.prop alethe.rare.prop alethe.quant;
require open Stdlib.Set Stdlib.Prop Stdlib.FOL;

constant symbol nat : Set;
constant symbol zero : τ nat;
constant symbol succ : τ nat → τ nat;
symbol even : τ nat → Prop;

symbol plus : τ nat → τ nat → τ nat;
rule plus zero $n ↪ $n;

symbol two ≔ succ (succ zero);

symbol P : (τ nat → Prop) → Prop;

// ==========================================================================
// Generated code for rule_unfold: the rule_unfold_* symbols below and its proof.
// ==========================================================================
symbol rule_unfold_p_1_ (nat : Set) (zero : (τ (nat))) (even : (τ (nat ⤳ o)))
  ≔ (even zero);
symbol rule_unfold_p_2_ (nat : Set) (zero : (τ (nat))) (even : (τ (nat ⤳ o)))
  ≔ (¬ ((rule_unfold_p_1_ nat zero even)));
opaque symbol rule_unfold_t0_ (nat : Set) (zero : (τ (nat))) (even : (τ (nat ⤳ o)))
  (a0 : π̇ ((rule_unfold_p_1_ nat zero even) ⸬ □))
  (hGoal : π̇ ((rule_unfold_p_2_ nat zero even) ⸬ □)) : π̇ □ ≔
begin
assume nat zero even a0;
  set p_1 ≔ (rule_unfold_p_1_ nat zero even);
  set p_2 ≔ (rule_unfold_p_2_ nat zero even);
  assume hGoal;
  refine (disj_resolutionN2 (p_1 ⸬ □) (p_2 ⸬ □) Stdlib.Nat.0
          Stdlib.Nat.0 a0 hGoal ⊤ᵢ ⊤ᵢ (eq_refl _))
    ;
end;
opaque symbol rule_unfold_a1_ (nat : Set) (zero : (τ (nat))) (even : (τ (nat ⤳ o)))
  (a0 : π̇ ((rule_unfold_p_1_ nat zero even) ⸬ □)) : π (rule_unfold_p_1_ nat zero even) ≔
begin
assume nat zero even a0;
  set p_1 ≔ (rule_unfold_p_1_ nat zero even);
  set p_2 ≔ (rule_unfold_p_2_ nat zero even);
  set t0 ≔ (rule_unfold_t0_ nat zero even a0);
  apply contradiction;
  assume hGoal;
  refine (t0 (clᵢ₁' hGoal));
end;

opaque symbol rule_unfold : π (even zero) → π (even (plus zero zero)) ≔
begin
  simplify plus;
  assume h0;
  refine
    (λ (nat' : Set)
        (zero' : τ (nat'))
        (even' : τ ((nat') Stdlib.HOL.⤳ Stdlib.Impred.o))
        (a0 : alethe.core.π̇ ((rule_unfold_p_1_ (nat') (zero') (even')) Stdlib.List.⸬ (Stdlib.List.□)))
        (goal : (π (rule_unfold_p_1_ (nat') (zero') (even'))) → π (even zero)),
        goal (rule_unfold_a1_ nat' zero' even' a0))
    _ _ _ _ _
    { admit } { admit } { admit } { admit } { admit };
end;

// ==========================================================================
// Generated code for def_unfold: the def_unfold_* symbols below and its proof.
// ==========================================================================
symbol def_unfold_p_1_ (nat : Set) (zero : (τ (nat))) (succ : (τ (nat ⤳ nat)))
  (even : (τ (nat ⤳ o))) ≔ (even zero);
symbol def_unfold_p_2_ (nat : Set) (zero : (τ (nat))) (succ : (τ (nat ⤳ nat)))
  (even : (τ (nat ⤳ o)))
  ≔ (∀ (λ (n : (τ (nat))), (((even n)) ⇒ ((even (succ (succ n)))))));
symbol def_unfold_p_3_ (nat : Set) (zero : (τ (nat))) (succ : (τ (nat ⤳ nat)))
  (even : (τ (nat ⤳ o))) ≔ (succ zero);
symbol def_unfold_p_4_ (nat : Set) (zero : (τ (nat))) (succ : (τ (nat ⤳ nat)))
  (even : (τ (nat ⤳ o))) ≔ (succ (def_unfold_p_3_ nat zero succ even));
symbol def_unfold_p_5_ (nat : Set) (zero : (τ (nat))) (succ : (τ (nat ⤳ nat)))
  (even : (τ (nat ⤳ o))) ≔ (even (def_unfold_p_4_ nat zero succ even));
symbol def_unfold_p_6_ (nat : Set) (zero : (τ (nat))) (succ : (τ (nat ⤳ nat)))
  (even : (τ (nat ⤳ o))) ≔ (¬ ((def_unfold_p_5_ nat zero succ even)));
symbol def_unfold_p_7_ (nat : Set) (zero : (τ (nat))) (succ : (τ (nat ⤳ nat)))
  (even : (τ (nat ⤳ o)))
  ≔ (∀
       (λ (n : (τ (nat))), ((¬ ((even n))) ∨ (even (succ (succ n))))));
symbol def_unfold_p_8_ (nat : Set) (zero : (τ (nat))) (succ : (τ (nat ⤳ nat)))
  (even : (τ (nat ⤳ o))) ≔ (¬ ((def_unfold_p_1_ nat zero succ even)));
symbol def_unfold_p_9_ (nat : Set) (zero : (τ (nat))) (succ : (τ (nat ⤳ nat)))
  (even : (τ (nat ⤳ o)))
  ≔ ((def_unfold_p_8_ nat zero succ even) ∨ (def_unfold_p_5_ nat zero succ even));
symbol def_unfold_p_10_ (nat : Set) (zero : (τ (nat))) (succ : (τ (nat ⤳ nat)))
  (even : (τ (nat ⤳ o)))
  ≔ (((def_unfold_p_7_ nat zero succ even)) ⇒ ((def_unfold_p_9_ nat zero succ even)));
symbol def_unfold_p_11_ (nat : Set) (zero : (τ (nat))) (succ : (τ (nat ⤳ nat)))
  (even : (τ (nat ⤳ o))) ≔ (¬ ((def_unfold_p_7_ nat zero succ even)));
symbol def_unfold_p_12_ (nat : Set) (zero : (τ (nat))) (succ : (τ (nat ⤳ nat)))
  (even : (τ (nat ⤳ o)))
  ≔ ((def_unfold_p_11_ nat zero succ even) ∨ (def_unfold_p_9_ nat zero succ even));
symbol def_unfold_p_13_ (nat : Set) (zero : (τ (nat))) (succ : (τ (nat ⤳ nat)))
  (even : (τ (nat ⤳ o)))
  ≔ ((def_unfold_p_2_ nat zero succ even) = (def_unfold_p_7_ nat zero succ even));
symbol def_unfold_p_14_ (nat : Set) (zero : (τ (nat))) (succ : (τ (nat ⤳ nat)))
  (even : (τ (nat ⤳ o))) ≔ (¬ ((def_unfold_p_13_ nat zero succ even)));
symbol def_unfold_p_15_ (nat : Set) (zero : (τ (nat))) (succ : (τ (nat ⤳ nat)))
  (even : (τ (nat ⤳ o))) ≔ (¬ ((def_unfold_p_2_ nat zero succ even)));
symbol def_unfold_p_16_ (nat : Set) (zero : (τ (nat))) (succ : (τ (nat ⤳ nat)))
  (even : (τ (nat ⤳ o))) ≔ (¬ ((def_unfold_p_9_ nat zero succ even)));
opaque symbol def_unfold_t0_ (nat : Set) (zero : (τ (nat))) (succ : (τ (nat ⤳ nat)))
  (even : (τ (nat ⤳ o))) (a0 : π̇ ((def_unfold_p_1_ nat zero succ even) ⸬ □))
  (a1 : π̇ ((def_unfold_p_2_ nat zero succ even) ⸬ □))
  : π̇ ((def_unfold_p_10_ nat zero succ even) ⸬ (def_unfold_p_7_ nat zero succ even) ⸬ □)
  ≔
begin
assume nat zero succ even a0 a1;
  set p_1 ≔ (def_unfold_p_1_ nat zero succ even);
  set p_2 ≔ (def_unfold_p_2_ nat zero succ even);
  set p_3 ≔ (def_unfold_p_3_ nat zero succ even);
  set p_4 ≔ (def_unfold_p_4_ nat zero succ even);
  set p_5 ≔ (def_unfold_p_5_ nat zero succ even);
  set p_6 ≔ (def_unfold_p_6_ nat zero succ even);
  set p_7 ≔ (def_unfold_p_7_ nat zero succ even);
  set p_8 ≔ (def_unfold_p_8_ nat zero succ even);
  set p_9 ≔ (def_unfold_p_9_ nat zero succ even);
  set p_10 ≔ (def_unfold_p_10_ nat zero succ even);
  set p_11 ≔ (def_unfold_p_11_ nat zero succ even);
  set p_12 ≔ (def_unfold_p_12_ nat zero succ even);
  set p_13 ≔ (def_unfold_p_13_ nat zero succ even);
  set p_14 ≔ (def_unfold_p_14_ nat zero succ even);
  set p_15 ≔ (def_unfold_p_15_ nat zero succ even);
  set p_16 ≔ (def_unfold_p_16_ nat zero succ even);
  apply (implies_neg1);
end;
opaque symbol def_unfold_t1_a0_ (nat : Set) (zero : (τ (nat)))
  (succ : (τ (nat ⤳ nat))) (even : (τ (nat ⤳ o)))
  (a0 : π̇ ((def_unfold_p_1_ nat zero succ even) ⸬ □))
  (a1 : π̇ ((def_unfold_p_2_ nat zero succ even) ⸬ □))
  : π̇ ((def_unfold_p_7_ nat zero succ even) ⸬ □) ≔
begin
assume nat zero succ even a0 a1;
  set p_1 ≔ (def_unfold_p_1_ nat zero succ even);
  set p_2 ≔ (def_unfold_p_2_ nat zero succ even);
  set p_3 ≔ (def_unfold_p_3_ nat zero succ even);
  set p_4 ≔ (def_unfold_p_4_ nat zero succ even);
  set p_5 ≔ (def_unfold_p_5_ nat zero succ even);
  set p_6 ≔ (def_unfold_p_6_ nat zero succ even);
  set p_7 ≔ (def_unfold_p_7_ nat zero succ even);
  set p_8 ≔ (def_unfold_p_8_ nat zero succ even);
  set p_9 ≔ (def_unfold_p_9_ nat zero succ even);
  set p_10 ≔ (def_unfold_p_10_ nat zero succ even);
  set p_11 ≔ (def_unfold_p_11_ nat zero succ even);
  set p_12 ≔ (def_unfold_p_12_ nat zero succ even);
  set p_13 ≔ (def_unfold_p_13_ nat zero succ even);
  set p_14 ≔ (def_unfold_p_14_ nat zero succ even);
  set p_15 ≔ (def_unfold_p_15_ nat zero succ even);
  set p_16 ≔ (def_unfold_p_16_ nat zero succ even);
  set t0 ≔ (def_unfold_t0_ nat zero succ even a0 a1);
  admit;
end;
opaque symbol def_unfold_t1_t0_ (nat : Set) (zero : (τ (nat)))
  (succ : (τ (nat ⤳ nat))) (even : (τ (nat ⤳ o)))
  (a0 : π̇ ((def_unfold_p_1_ nat zero succ even) ⸬ □))
  (a1 : π̇ ((def_unfold_p_2_ nat zero succ even) ⸬ □))
  : π̇ ((def_unfold_p_12_ nat zero succ even) ⸬ □) ≔
begin
assume nat zero succ even a0 a1;
  set p_1 ≔ (def_unfold_p_1_ nat zero succ even);
  set p_2 ≔ (def_unfold_p_2_ nat zero succ even);
  set p_3 ≔ (def_unfold_p_3_ nat zero succ even);
  set p_4 ≔ (def_unfold_p_4_ nat zero succ even);
  set p_5 ≔ (def_unfold_p_5_ nat zero succ even);
  set p_6 ≔ (def_unfold_p_6_ nat zero succ even);
  set p_7 ≔ (def_unfold_p_7_ nat zero succ even);
  set p_8 ≔ (def_unfold_p_8_ nat zero succ even);
  set p_9 ≔ (def_unfold_p_9_ nat zero succ even);
  set p_10 ≔ (def_unfold_p_10_ nat zero succ even);
  set p_11 ≔ (def_unfold_p_11_ nat zero succ even);
  set p_12 ≔ (def_unfold_p_12_ nat zero succ even);
  set p_13 ≔ (def_unfold_p_13_ nat zero succ even);
  set p_14 ≔ (def_unfold_p_14_ nat zero succ even);
  set p_15 ≔ (def_unfold_p_15_ nat zero succ even);
  set p_16 ≔ (def_unfold_p_16_ nat zero succ even);
  set t0 ≔ (def_unfold_t0_ nat zero succ even a0 a1);
  set t1_a0 ≔ (def_unfold_t1_a0_ nat zero succ even a0 a1);
  apply ∨ᵢ₁;
  apply imply_to_or;
  assume H;
  refine (H zero);
end;
opaque symbol def_unfold_t1_t1_ (nat : Set) (zero : (τ (nat)))
  (succ : (τ (nat ⤳ nat))) (even : (τ (nat ⤳ o)))
  (a0 : π̇ ((def_unfold_p_1_ nat zero succ even) ⸬ □))
  (a1 : π̇ ((def_unfold_p_2_ nat zero succ even) ⸬ □))
  : π̇ ((def_unfold_p_11_ nat zero succ even) ⸬ (def_unfold_p_9_ nat zero succ even) ⸬ □)
  ≔
begin
assume nat zero succ even a0 a1;
  set p_1 ≔ (def_unfold_p_1_ nat zero succ even);
  set p_2 ≔ (def_unfold_p_2_ nat zero succ even);
  set p_3 ≔ (def_unfold_p_3_ nat zero succ even);
  set p_4 ≔ (def_unfold_p_4_ nat zero succ even);
  set p_5 ≔ (def_unfold_p_5_ nat zero succ even);
  set p_6 ≔ (def_unfold_p_6_ nat zero succ even);
  set p_7 ≔ (def_unfold_p_7_ nat zero succ even);
  set p_8 ≔ (def_unfold_p_8_ nat zero succ even);
  set p_9 ≔ (def_unfold_p_9_ nat zero succ even);
  set p_10 ≔ (def_unfold_p_10_ nat zero succ even);
  set p_11 ≔ (def_unfold_p_11_ nat zero succ even);
  set p_12 ≔ (def_unfold_p_12_ nat zero succ even);
  set p_13 ≔ (def_unfold_p_13_ nat zero succ even);
  set p_14 ≔ (def_unfold_p_14_ nat zero succ even);
  set p_15 ≔ (def_unfold_p_15_ nat zero succ even);
  set p_16 ≔ (def_unfold_p_16_ nat zero succ even);
  set t0 ≔ (def_unfold_t0_ nat zero succ even a0 a1);
  set t1_a0 ≔ (def_unfold_t1_a0_ nat zero succ even a0 a1);
  set t1_t0 ≔ (def_unfold_t1_t0_ nat zero succ even a0 a1);
  refine (∨ₑₙ (p_11 ⸬ p_9 ⸬ □) _);
  simplify;
  eval #repeat_or_id_r;
  refine (π̇ₗ t1_t0);
end;
opaque symbol def_unfold_t1_t2_ (nat : Set) (zero : (τ (nat)))
  (succ : (τ (nat ⤳ nat))) (even : (τ (nat ⤳ o)))
  (a0 : π̇ ((def_unfold_p_1_ nat zero succ even) ⸬ □))
  (a1 : π̇ ((def_unfold_p_2_ nat zero succ even) ⸬ □))
  : π̇
    ((def_unfold_p_14_ nat zero succ even) ⸬ (def_unfold_p_15_ nat zero succ even) ⸬
     (def_unfold_p_7_ nat zero succ even) ⸬ □)
  ≔
begin
assume nat zero succ even a0 a1;
  set p_1 ≔ (def_unfold_p_1_ nat zero succ even);
  set p_2 ≔ (def_unfold_p_2_ nat zero succ even);
  set p_3 ≔ (def_unfold_p_3_ nat zero succ even);
  set p_4 ≔ (def_unfold_p_4_ nat zero succ even);
  set p_5 ≔ (def_unfold_p_5_ nat zero succ even);
  set p_6 ≔ (def_unfold_p_6_ nat zero succ even);
  set p_7 ≔ (def_unfold_p_7_ nat zero succ even);
  set p_8 ≔ (def_unfold_p_8_ nat zero succ even);
  set p_9 ≔ (def_unfold_p_9_ nat zero succ even);
  set p_10 ≔ (def_unfold_p_10_ nat zero succ even);
  set p_11 ≔ (def_unfold_p_11_ nat zero succ even);
  set p_12 ≔ (def_unfold_p_12_ nat zero succ even);
  set p_13 ≔ (def_unfold_p_13_ nat zero succ even);
  set p_14 ≔ (def_unfold_p_14_ nat zero succ even);
  set p_15 ≔ (def_unfold_p_15_ nat zero succ even);
  set p_16 ≔ (def_unfold_p_16_ nat zero succ even);
  set t0 ≔ (def_unfold_t0_ nat zero succ even a0 a1);
  set t1_a0 ≔ (def_unfold_t1_a0_ nat zero succ even a0 a1);
  set t1_t0 ≔ (def_unfold_t1_t0_ nat zero succ even a0 a1);
  set t1_t1 ≔ (def_unfold_t1_t1_ nat zero succ even a0 a1);
  apply (equiv_pos2);
end;
opaque symbol def_unfold_t1_t3_ (nat : Set) (zero : (τ (nat)))
  (succ : (τ (nat ⤳ nat))) (even : (τ (nat ⤳ o)))
  (a0 : π̇ ((def_unfold_p_1_ nat zero succ even) ⸬ □))
  (a1 : π̇ ((def_unfold_p_2_ nat zero succ even) ⸬ □))
  : π̇ ((def_unfold_p_13_ nat zero succ even) ⸬ □) ≔
begin
assume nat zero succ even a0 a1;
  set p_1 ≔ (def_unfold_p_1_ nat zero succ even);
  set p_2 ≔ (def_unfold_p_2_ nat zero succ even);
  set p_3 ≔ (def_unfold_p_3_ nat zero succ even);
  set p_4 ≔ (def_unfold_p_4_ nat zero succ even);
  set p_5 ≔ (def_unfold_p_5_ nat zero succ even);
  set p_6 ≔ (def_unfold_p_6_ nat zero succ even);
  set p_7 ≔ (def_unfold_p_7_ nat zero succ even);
  set p_8 ≔ (def_unfold_p_8_ nat zero succ even);
  set p_9 ≔ (def_unfold_p_9_ nat zero succ even);
  set p_10 ≔ (def_unfold_p_10_ nat zero succ even);
  set p_11 ≔ (def_unfold_p_11_ nat zero succ even);
  set p_12 ≔ (def_unfold_p_12_ nat zero succ even);
  set p_13 ≔ (def_unfold_p_13_ nat zero succ even);
  set p_14 ≔ (def_unfold_p_14_ nat zero succ even);
  set p_15 ≔ (def_unfold_p_15_ nat zero succ even);
  set p_16 ≔ (def_unfold_p_16_ nat zero succ even);
  set t0 ≔ (def_unfold_t0_ nat zero succ even a0 a1);
  set t1_a0 ≔ (def_unfold_t1_a0_ nat zero succ even a0 a1);
  set t1_t0 ≔ (def_unfold_t1_t0_ nat zero succ even a0 a1);
  set t1_t1 ≔ (def_unfold_t1_t1_ nat zero succ even a0 a1);
  set t1_t2 ≔ (def_unfold_t1_t2_ nat zero succ even a0 a1);
  apply ∨ᵢ₁;
  apply bind_∀;
  assume n;
  have t1_t3_t0: π̇
                 (((((even n)) ⇒ ((even (succ (succ n))))) =
                   ((¬ ((even n))) ∨ (even (succ (succ n)))))
                  ⸬ □)
    { apply ∨ᵢ₁; rewrite bool-impl-elim; reflexivity; };
  apply (π̇ₗ t1_t3_t0);
end;
opaque symbol def_unfold_t1_t4_ (nat : Set) (zero : (τ (nat)))
  (succ : (τ (nat ⤳ nat))) (even : (τ (nat ⤳ o)))
  (a0 : π̇ ((def_unfold_p_1_ nat zero succ even) ⸬ □))
  (a1 : π̇ ((def_unfold_p_2_ nat zero succ even) ⸬ □))
  : π̇ ((def_unfold_p_7_ nat zero succ even) ⸬ □) ≔
begin
assume nat zero succ even a0 a1;
  set p_1 ≔ (def_unfold_p_1_ nat zero succ even);
  set p_2 ≔ (def_unfold_p_2_ nat zero succ even);
  set p_3 ≔ (def_unfold_p_3_ nat zero succ even);
  set p_4 ≔ (def_unfold_p_4_ nat zero succ even);
  set p_5 ≔ (def_unfold_p_5_ nat zero succ even);
  set p_6 ≔ (def_unfold_p_6_ nat zero succ even);
  set p_7 ≔ (def_unfold_p_7_ nat zero succ even);
  set p_8 ≔ (def_unfold_p_8_ nat zero succ even);
  set p_9 ≔ (def_unfold_p_9_ nat zero succ even);
  set p_10 ≔ (def_unfold_p_10_ nat zero succ even);
  set p_11 ≔ (def_unfold_p_11_ nat zero succ even);
  set p_12 ≔ (def_unfold_p_12_ nat zero succ even);
  set p_13 ≔ (def_unfold_p_13_ nat zero succ even);
  set p_14 ≔ (def_unfold_p_14_ nat zero succ even);
  set p_15 ≔ (def_unfold_p_15_ nat zero succ even);
  set p_16 ≔ (def_unfold_p_16_ nat zero succ even);
  set t0 ≔ (def_unfold_t0_ nat zero succ even a0 a1);
  set t1_a0 ≔ (def_unfold_t1_a0_ nat zero succ even a0 a1);
  set t1_t0 ≔ (def_unfold_t1_t0_ nat zero succ even a0 a1);
  set t1_t1 ≔ (def_unfold_t1_t1_ nat zero succ even a0 a1);
  set t1_t2 ≔ (def_unfold_t1_t2_ nat zero succ even a0 a1);
  set t1_t3 ≔ (def_unfold_t1_t3_ nat zero succ even a0 a1);
  refine (disj_resolutionN1 (p_15 ⸬ p_7 ⸬ □) (p_2 ⸬ □) Stdlib.Nat.0
          Stdlib.Nat.0
          (disj_resolutionN1 (p_14 ⸬ p_15 ⸬ p_7 ⸬ □) (p_13 ⸬ □)
           Stdlib.Nat.0 Stdlib.Nat.0 t1_t2 t1_t3 ⊤ᵢ ⊤ᵢ (eq_refl _))
          a1 ⊤ᵢ ⊤ᵢ (eq_refl _))
    ;
end;
opaque symbol def_unfold_t1_t5_ (nat : Set) (zero : (τ (nat)))
  (succ : (τ (nat ⤳ nat))) (even : (τ (nat ⤳ o)))
  (a0 : π̇ ((def_unfold_p_1_ nat zero succ even) ⸬ □))
  (a1 : π̇ ((def_unfold_p_2_ nat zero succ even) ⸬ □))
  : π̇ ((def_unfold_p_9_ nat zero succ even) ⸬ □) ≔
begin
assume nat zero succ even a0 a1;
  set p_1 ≔ (def_unfold_p_1_ nat zero succ even);
  set p_2 ≔ (def_unfold_p_2_ nat zero succ even);
  set p_3 ≔ (def_unfold_p_3_ nat zero succ even);
  set p_4 ≔ (def_unfold_p_4_ nat zero succ even);
  set p_5 ≔ (def_unfold_p_5_ nat zero succ even);
  set p_6 ≔ (def_unfold_p_6_ nat zero succ even);
  set p_7 ≔ (def_unfold_p_7_ nat zero succ even);
  set p_8 ≔ (def_unfold_p_8_ nat zero succ even);
  set p_9 ≔ (def_unfold_p_9_ nat zero succ even);
  set p_10 ≔ (def_unfold_p_10_ nat zero succ even);
  set p_11 ≔ (def_unfold_p_11_ nat zero succ even);
  set p_12 ≔ (def_unfold_p_12_ nat zero succ even);
  set p_13 ≔ (def_unfold_p_13_ nat zero succ even);
  set p_14 ≔ (def_unfold_p_14_ nat zero succ even);
  set p_15 ≔ (def_unfold_p_15_ nat zero succ even);
  set p_16 ≔ (def_unfold_p_16_ nat zero succ even);
  set t0 ≔ (def_unfold_t0_ nat zero succ even a0 a1);
  set t1_a0 ≔ (def_unfold_t1_a0_ nat zero succ even a0 a1);
  set t1_t0 ≔ (def_unfold_t1_t0_ nat zero succ even a0 a1);
  set t1_t1 ≔ (def_unfold_t1_t1_ nat zero succ even a0 a1);
  set t1_t2 ≔ (def_unfold_t1_t2_ nat zero succ even a0 a1);
  set t1_t3 ≔ (def_unfold_t1_t3_ nat zero succ even a0 a1);
  set t1_t4 ≔ (def_unfold_t1_t4_ nat zero succ even a0 a1);
  refine (disj_resolutionN1 (p_11 ⸬ p_9 ⸬ □) (p_7 ⸬ □) Stdlib.Nat.0
          Stdlib.Nat.0 t1_t1 t1_t4 ⊤ᵢ ⊤ᵢ (eq_refl _))
    ;
end;
opaque symbol def_unfold_t1_ (nat : Set) (zero : (τ (nat))) (succ : (τ (nat ⤳ nat)))
  (even : (τ (nat ⤳ o))) (a0 : π̇ ((def_unfold_p_1_ nat zero succ even) ⸬ □))
  (a1 : π̇ ((def_unfold_p_2_ nat zero succ even) ⸬ □))
  : π̇ ((def_unfold_p_11_ nat zero succ even) ⸬ (def_unfold_p_9_ nat zero succ even) ⸬ □)
  ≔
begin
assume nat zero succ even a0 a1;
  set p_1 ≔ (def_unfold_p_1_ nat zero succ even);
  set p_2 ≔ (def_unfold_p_2_ nat zero succ even);
  set p_3 ≔ (def_unfold_p_3_ nat zero succ even);
  set p_4 ≔ (def_unfold_p_4_ nat zero succ even);
  set p_5 ≔ (def_unfold_p_5_ nat zero succ even);
  set p_6 ≔ (def_unfold_p_6_ nat zero succ even);
  set p_7 ≔ (def_unfold_p_7_ nat zero succ even);
  set p_8 ≔ (def_unfold_p_8_ nat zero succ even);
  set p_9 ≔ (def_unfold_p_9_ nat zero succ even);
  set p_10 ≔ (def_unfold_p_10_ nat zero succ even);
  set p_11 ≔ (def_unfold_p_11_ nat zero succ even);
  set p_12 ≔ (def_unfold_p_12_ nat zero succ even);
  set p_13 ≔ (def_unfold_p_13_ nat zero succ even);
  set p_14 ≔ (def_unfold_p_14_ nat zero succ even);
  set p_15 ≔ (def_unfold_p_15_ nat zero succ even);
  set p_16 ≔ (def_unfold_p_16_ nat zero succ even);
  set t0 ≔ (def_unfold_t0_ nat zero succ even a0 a1);
  set t1_a0 ≔ (def_unfold_t1_a0_ nat zero succ even a0 a1);
  set t1_t0 ≔ (def_unfold_t1_t0_ nat zero succ even a0 a1);
  set t1_t1 ≔ (def_unfold_t1_t1_ nat zero succ even a0 a1);
  set t1_t2 ≔ (def_unfold_t1_t2_ nat zero succ even a0 a1);
  set t1_t3 ≔ (def_unfold_t1_t3_ nat zero succ even a0 a1);
  set t1_t4 ≔ (def_unfold_t1_t4_ nat zero succ even a0 a1);
  set t1_t5 ≔ (def_unfold_t1_t5_ nat zero succ even a0 a1);
  apply ∨ᵢ₂;
  apply ∨ᵢ₁;
  apply (π̇ₗ t1_t5);
end;
opaque symbol def_unfold_t2_ (nat : Set) (zero : (τ (nat))) (succ : (τ (nat ⤳ nat)))
  (even : (τ (nat ⤳ o))) (a0 : π̇ ((def_unfold_p_1_ nat zero succ even) ⸬ □))
  (a1 : π̇ ((def_unfold_p_2_ nat zero succ even) ⸬ □))
  : π̇ ((def_unfold_p_10_ nat zero succ even) ⸬ (def_unfold_p_9_ nat zero succ even) ⸬ □)
  ≔
begin
assume nat zero succ even a0 a1;
  set p_1 ≔ (def_unfold_p_1_ nat zero succ even);
  set p_2 ≔ (def_unfold_p_2_ nat zero succ even);
  set p_3 ≔ (def_unfold_p_3_ nat zero succ even);
  set p_4 ≔ (def_unfold_p_4_ nat zero succ even);
  set p_5 ≔ (def_unfold_p_5_ nat zero succ even);
  set p_6 ≔ (def_unfold_p_6_ nat zero succ even);
  set p_7 ≔ (def_unfold_p_7_ nat zero succ even);
  set p_8 ≔ (def_unfold_p_8_ nat zero succ even);
  set p_9 ≔ (def_unfold_p_9_ nat zero succ even);
  set p_10 ≔ (def_unfold_p_10_ nat zero succ even);
  set p_11 ≔ (def_unfold_p_11_ nat zero succ even);
  set p_12 ≔ (def_unfold_p_12_ nat zero succ even);
  set p_13 ≔ (def_unfold_p_13_ nat zero succ even);
  set p_14 ≔ (def_unfold_p_14_ nat zero succ even);
  set p_15 ≔ (def_unfold_p_15_ nat zero succ even);
  set p_16 ≔ (def_unfold_p_16_ nat zero succ even);
  set t0 ≔ (def_unfold_t0_ nat zero succ even a0 a1);
  set t1_a0 ≔ (def_unfold_t1_a0_ nat zero succ even a0 a1);
  set t1_t0 ≔ (def_unfold_t1_t0_ nat zero succ even a0 a1);
  set t1_t1 ≔ (def_unfold_t1_t1_ nat zero succ even a0 a1);
  set t1_t2 ≔ (def_unfold_t1_t2_ nat zero succ even a0 a1);
  set t1_t3 ≔ (def_unfold_t1_t3_ nat zero succ even a0 a1);
  set t1_t4 ≔ (def_unfold_t1_t4_ nat zero succ even a0 a1);
  set t1_t5 ≔ (def_unfold_t1_t5_ nat zero succ even a0 a1);
  set t1 ≔ (def_unfold_t1_ nat zero succ even a0 a1);
  refine (disj_resolutionN2 (p_10 ⸬ p_7 ⸬ □) (p_11 ⸬ p_9 ⸬ □)
          Stdlib.Nat.1 Stdlib.Nat.0 t0 t1 ⊤ᵢ ⊤ᵢ (eq_refl _))
    ;
end;
opaque symbol def_unfold_t3_ (nat : Set) (zero : (τ (nat))) (succ : (τ (nat ⤳ nat)))
  (even : (τ (nat ⤳ o))) (a0 : π̇ ((def_unfold_p_1_ nat zero succ even) ⸬ □))
  (a1 : π̇ ((def_unfold_p_2_ nat zero succ even) ⸬ □))
  : π̇ ((def_unfold_p_10_ nat zero succ even) ⸬ (def_unfold_p_16_ nat zero succ even) ⸬ □)
  ≔
begin
assume nat zero succ even a0 a1;
  set p_1 ≔ (def_unfold_p_1_ nat zero succ even);
  set p_2 ≔ (def_unfold_p_2_ nat zero succ even);
  set p_3 ≔ (def_unfold_p_3_ nat zero succ even);
  set p_4 ≔ (def_unfold_p_4_ nat zero succ even);
  set p_5 ≔ (def_unfold_p_5_ nat zero succ even);
  set p_6 ≔ (def_unfold_p_6_ nat zero succ even);
  set p_7 ≔ (def_unfold_p_7_ nat zero succ even);
  set p_8 ≔ (def_unfold_p_8_ nat zero succ even);
  set p_9 ≔ (def_unfold_p_9_ nat zero succ even);
  set p_10 ≔ (def_unfold_p_10_ nat zero succ even);
  set p_11 ≔ (def_unfold_p_11_ nat zero succ even);
  set p_12 ≔ (def_unfold_p_12_ nat zero succ even);
  set p_13 ≔ (def_unfold_p_13_ nat zero succ even);
  set p_14 ≔ (def_unfold_p_14_ nat zero succ even);
  set p_15 ≔ (def_unfold_p_15_ nat zero succ even);
  set p_16 ≔ (def_unfold_p_16_ nat zero succ even);
  set t0 ≔ (def_unfold_t0_ nat zero succ even a0 a1);
  set t1_a0 ≔ (def_unfold_t1_a0_ nat zero succ even a0 a1);
  set t1_t0 ≔ (def_unfold_t1_t0_ nat zero succ even a0 a1);
  set t1_t1 ≔ (def_unfold_t1_t1_ nat zero succ even a0 a1);
  set t1_t2 ≔ (def_unfold_t1_t2_ nat zero succ even a0 a1);
  set t1_t3 ≔ (def_unfold_t1_t3_ nat zero succ even a0 a1);
  set t1_t4 ≔ (def_unfold_t1_t4_ nat zero succ even a0 a1);
  set t1_t5 ≔ (def_unfold_t1_t5_ nat zero succ even a0 a1);
  set t1 ≔ (def_unfold_t1_ nat zero succ even a0 a1);
  set t2 ≔ (def_unfold_t2_ nat zero succ even a0 a1);
  apply (implies_neg2);
end;
opaque symbol def_unfold_t4_ (nat : Set) (zero : (τ (nat))) (succ : (τ (nat ⤳ nat)))
  (even : (τ (nat ⤳ o))) (a0 : π̇ ((def_unfold_p_1_ nat zero succ even) ⸬ □))
  (a1 : π̇ ((def_unfold_p_2_ nat zero succ even) ⸬ □))
  : π̇ ((def_unfold_p_10_ nat zero succ even) ⸬ (def_unfold_p_10_ nat zero succ even) ⸬ □)
  ≔
begin
assume nat zero succ even a0 a1;
  set p_1 ≔ (def_unfold_p_1_ nat zero succ even);
  set p_2 ≔ (def_unfold_p_2_ nat zero succ even);
  set p_3 ≔ (def_unfold_p_3_ nat zero succ even);
  set p_4 ≔ (def_unfold_p_4_ nat zero succ even);
  set p_5 ≔ (def_unfold_p_5_ nat zero succ even);
  set p_6 ≔ (def_unfold_p_6_ nat zero succ even);
  set p_7 ≔ (def_unfold_p_7_ nat zero succ even);
  set p_8 ≔ (def_unfold_p_8_ nat zero succ even);
  set p_9 ≔ (def_unfold_p_9_ nat zero succ even);
  set p_10 ≔ (def_unfold_p_10_ nat zero succ even);
  set p_11 ≔ (def_unfold_p_11_ nat zero succ even);
  set p_12 ≔ (def_unfold_p_12_ nat zero succ even);
  set p_13 ≔ (def_unfold_p_13_ nat zero succ even);
  set p_14 ≔ (def_unfold_p_14_ nat zero succ even);
  set p_15 ≔ (def_unfold_p_15_ nat zero succ even);
  set p_16 ≔ (def_unfold_p_16_ nat zero succ even);
  set t0 ≔ (def_unfold_t0_ nat zero succ even a0 a1);
  set t1_a0 ≔ (def_unfold_t1_a0_ nat zero succ even a0 a1);
  set t1_t0 ≔ (def_unfold_t1_t0_ nat zero succ even a0 a1);
  set t1_t1 ≔ (def_unfold_t1_t1_ nat zero succ even a0 a1);
  set t1_t2 ≔ (def_unfold_t1_t2_ nat zero succ even a0 a1);
  set t1_t3 ≔ (def_unfold_t1_t3_ nat zero succ even a0 a1);
  set t1_t4 ≔ (def_unfold_t1_t4_ nat zero succ even a0 a1);
  set t1_t5 ≔ (def_unfold_t1_t5_ nat zero succ even a0 a1);
  set t1 ≔ (def_unfold_t1_ nat zero succ even a0 a1);
  set t2 ≔ (def_unfold_t2_ nat zero succ even a0 a1);
  set t3 ≔ (def_unfold_t3_ nat zero succ even a0 a1);
  refine (disj_resolutionN2 (p_10 ⸬ p_9 ⸬ □) (p_10 ⸬ p_16 ⸬ □)
          Stdlib.Nat.1 Stdlib.Nat.1 t2 t3 ⊤ᵢ ⊤ᵢ (eq_refl _))
    ;
end;
opaque symbol def_unfold_t5_ (nat : Set) (zero : (τ (nat))) (succ : (τ (nat ⤳ nat)))
  (even : (τ (nat ⤳ o))) (a0 : π̇ ((def_unfold_p_1_ nat zero succ even) ⸬ □))
  (a1 : π̇ ((def_unfold_p_2_ nat zero succ even) ⸬ □))
  : π̇ ((def_unfold_p_10_ nat zero succ even) ⸬ □) ≔
begin
assume nat zero succ even a0 a1;
  set p_1 ≔ (def_unfold_p_1_ nat zero succ even);
  set p_2 ≔ (def_unfold_p_2_ nat zero succ even);
  set p_3 ≔ (def_unfold_p_3_ nat zero succ even);
  set p_4 ≔ (def_unfold_p_4_ nat zero succ even);
  set p_5 ≔ (def_unfold_p_5_ nat zero succ even);
  set p_6 ≔ (def_unfold_p_6_ nat zero succ even);
  set p_7 ≔ (def_unfold_p_7_ nat zero succ even);
  set p_8 ≔ (def_unfold_p_8_ nat zero succ even);
  set p_9 ≔ (def_unfold_p_9_ nat zero succ even);
  set p_10 ≔ (def_unfold_p_10_ nat zero succ even);
  set p_11 ≔ (def_unfold_p_11_ nat zero succ even);
  set p_12 ≔ (def_unfold_p_12_ nat zero succ even);
  set p_13 ≔ (def_unfold_p_13_ nat zero succ even);
  set p_14 ≔ (def_unfold_p_14_ nat zero succ even);
  set p_15 ≔ (def_unfold_p_15_ nat zero succ even);
  set p_16 ≔ (def_unfold_p_16_ nat zero succ even);
  set t0 ≔ (def_unfold_t0_ nat zero succ even a0 a1);
  set t1_a0 ≔ (def_unfold_t1_a0_ nat zero succ even a0 a1);
  set t1_t0 ≔ (def_unfold_t1_t0_ nat zero succ even a0 a1);
  set t1_t1 ≔ (def_unfold_t1_t1_ nat zero succ even a0 a1);
  set t1_t2 ≔ (def_unfold_t1_t2_ nat zero succ even a0 a1);
  set t1_t3 ≔ (def_unfold_t1_t3_ nat zero succ even a0 a1);
  set t1_t4 ≔ (def_unfold_t1_t4_ nat zero succ even a0 a1);
  set t1_t5 ≔ (def_unfold_t1_t5_ nat zero succ even a0 a1);
  set t1 ≔ (def_unfold_t1_ nat zero succ even a0 a1);
  set t2 ≔ (def_unfold_t2_ nat zero succ even a0 a1);
  set t3 ≔ (def_unfold_t3_ nat zero succ even a0 a1);
  set t4 ≔ (def_unfold_t4_ nat zero succ even a0 a1);
  set ir ≔ (reify_cl (p_10 ⸬ p_10 ⸬ □));
  have H: π ((disj (p_10 ⸬ p_10 ⸬ □)) = (disj (p_10 ⸬ □)))
    {
       change π ((den (ir ₂) (ir ₁)) = (disj (p_10 ⸬ □)));
       rewrite left contraction_correct;
       reflexivity;
       };
  refine (subst_equiv_clause (p_10 ⸬ p_10 ⸬ □) (p_10 ⸬ □) H t4);
end;
opaque symbol def_unfold_t6_ (nat : Set) (zero : (τ (nat))) (succ : (τ (nat ⤳ nat)))
  (even : (τ (nat ⤳ o))) (a0 : π̇ ((def_unfold_p_1_ nat zero succ even) ⸬ □))
  (a1 : π̇ ((def_unfold_p_2_ nat zero succ even) ⸬ □))
  : π̇ ((def_unfold_p_11_ nat zero succ even) ⸬ (def_unfold_p_9_ nat zero succ even) ⸬ □)
  ≔
begin
assume nat zero succ even a0 a1;
  set p_1 ≔ (def_unfold_p_1_ nat zero succ even);
  set p_2 ≔ (def_unfold_p_2_ nat zero succ even);
  set p_3 ≔ (def_unfold_p_3_ nat zero succ even);
  set p_4 ≔ (def_unfold_p_4_ nat zero succ even);
  set p_5 ≔ (def_unfold_p_5_ nat zero succ even);
  set p_6 ≔ (def_unfold_p_6_ nat zero succ even);
  set p_7 ≔ (def_unfold_p_7_ nat zero succ even);
  set p_8 ≔ (def_unfold_p_8_ nat zero succ even);
  set p_9 ≔ (def_unfold_p_9_ nat zero succ even);
  set p_10 ≔ (def_unfold_p_10_ nat zero succ even);
  set p_11 ≔ (def_unfold_p_11_ nat zero succ even);
  set p_12 ≔ (def_unfold_p_12_ nat zero succ even);
  set p_13 ≔ (def_unfold_p_13_ nat zero succ even);
  set p_14 ≔ (def_unfold_p_14_ nat zero succ even);
  set p_15 ≔ (def_unfold_p_15_ nat zero succ even);
  set p_16 ≔ (def_unfold_p_16_ nat zero succ even);
  set t0 ≔ (def_unfold_t0_ nat zero succ even a0 a1);
  set t1_a0 ≔ (def_unfold_t1_a0_ nat zero succ even a0 a1);
  set t1_t0 ≔ (def_unfold_t1_t0_ nat zero succ even a0 a1);
  set t1_t1 ≔ (def_unfold_t1_t1_ nat zero succ even a0 a1);
  set t1_t2 ≔ (def_unfold_t1_t2_ nat zero succ even a0 a1);
  set t1_t3 ≔ (def_unfold_t1_t3_ nat zero succ even a0 a1);
  set t1_t4 ≔ (def_unfold_t1_t4_ nat zero succ even a0 a1);
  set t1_t5 ≔ (def_unfold_t1_t5_ nat zero succ even a0 a1);
  set t1 ≔ (def_unfold_t1_ nat zero succ even a0 a1);
  set t2 ≔ (def_unfold_t2_ nat zero succ even a0 a1);
  set t3 ≔ (def_unfold_t3_ nat zero succ even a0 a1);
  set t4 ≔ (def_unfold_t4_ nat zero succ even a0 a1);
  set t5 ≔ (def_unfold_t5_ nat zero succ even a0 a1);
  apply (implies (π̇ₗ t5));
end;
opaque symbol def_unfold_t7_ (nat : Set) (zero : (τ (nat))) (succ : (τ (nat ⤳ nat)))
  (even : (τ (nat ⤳ o))) (a0 : π̇ ((def_unfold_p_1_ nat zero succ even) ⸬ □))
  (a1 : π̇ ((def_unfold_p_2_ nat zero succ even) ⸬ □))
  : π̇
    ((def_unfold_p_16_ nat zero succ even) ⸬ (def_unfold_p_8_ nat zero succ even) ⸬
     (def_unfold_p_5_ nat zero succ even) ⸬ □)
  ≔
begin
assume nat zero succ even a0 a1;
  set p_1 ≔ (def_unfold_p_1_ nat zero succ even);
  set p_2 ≔ (def_unfold_p_2_ nat zero succ even);
  set p_3 ≔ (def_unfold_p_3_ nat zero succ even);
  set p_4 ≔ (def_unfold_p_4_ nat zero succ even);
  set p_5 ≔ (def_unfold_p_5_ nat zero succ even);
  set p_6 ≔ (def_unfold_p_6_ nat zero succ even);
  set p_7 ≔ (def_unfold_p_7_ nat zero succ even);
  set p_8 ≔ (def_unfold_p_8_ nat zero succ even);
  set p_9 ≔ (def_unfold_p_9_ nat zero succ even);
  set p_10 ≔ (def_unfold_p_10_ nat zero succ even);
  set p_11 ≔ (def_unfold_p_11_ nat zero succ even);
  set p_12 ≔ (def_unfold_p_12_ nat zero succ even);
  set p_13 ≔ (def_unfold_p_13_ nat zero succ even);
  set p_14 ≔ (def_unfold_p_14_ nat zero succ even);
  set p_15 ≔ (def_unfold_p_15_ nat zero succ even);
  set p_16 ≔ (def_unfold_p_16_ nat zero succ even);
  set t0 ≔ (def_unfold_t0_ nat zero succ even a0 a1);
  set t1_a0 ≔ (def_unfold_t1_a0_ nat zero succ even a0 a1);
  set t1_t0 ≔ (def_unfold_t1_t0_ nat zero succ even a0 a1);
  set t1_t1 ≔ (def_unfold_t1_t1_ nat zero succ even a0 a1);
  set t1_t2 ≔ (def_unfold_t1_t2_ nat zero succ even a0 a1);
  set t1_t3 ≔ (def_unfold_t1_t3_ nat zero succ even a0 a1);
  set t1_t4 ≔ (def_unfold_t1_t4_ nat zero succ even a0 a1);
  set t1_t5 ≔ (def_unfold_t1_t5_ nat zero succ even a0 a1);
  set t1 ≔ (def_unfold_t1_ nat zero succ even a0 a1);
  set t2 ≔ (def_unfold_t2_ nat zero succ even a0 a1);
  set t3 ≔ (def_unfold_t3_ nat zero succ even a0 a1);
  set t4 ≔ (def_unfold_t4_ nat zero succ even a0 a1);
  set t5 ≔ (def_unfold_t5_ nat zero succ even a0 a1);
  set t6 ≔ (def_unfold_t6_ nat zero succ even a0 a1);
  admit;
end;
opaque symbol def_unfold_t9_ (nat : Set) (zero : (τ (nat))) (succ : (τ (nat ⤳ nat)))
  (even : (τ (nat ⤳ o))) (a0 : π̇ ((def_unfold_p_1_ nat zero succ even) ⸬ □))
  (a1 : π̇ ((def_unfold_p_2_ nat zero succ even) ⸬ □))
  (hGoal : π̇ ((def_unfold_p_6_ nat zero succ even) ⸬ □))
  : π̇ ((def_unfold_p_16_ nat zero succ even) ⸬ □) ≔
begin
assume nat zero succ even a0 a1;
  set p_1 ≔ (def_unfold_p_1_ nat zero succ even);
  set p_2 ≔ (def_unfold_p_2_ nat zero succ even);
  set p_3 ≔ (def_unfold_p_3_ nat zero succ even);
  set p_4 ≔ (def_unfold_p_4_ nat zero succ even);
  set p_5 ≔ (def_unfold_p_5_ nat zero succ even);
  set p_6 ≔ (def_unfold_p_6_ nat zero succ even);
  set p_7 ≔ (def_unfold_p_7_ nat zero succ even);
  set p_8 ≔ (def_unfold_p_8_ nat zero succ even);
  set p_9 ≔ (def_unfold_p_9_ nat zero succ even);
  set p_10 ≔ (def_unfold_p_10_ nat zero succ even);
  set p_11 ≔ (def_unfold_p_11_ nat zero succ even);
  set p_12 ≔ (def_unfold_p_12_ nat zero succ even);
  set p_13 ≔ (def_unfold_p_13_ nat zero succ even);
  set p_14 ≔ (def_unfold_p_14_ nat zero succ even);
  set p_15 ≔ (def_unfold_p_15_ nat zero succ even);
  set p_16 ≔ (def_unfold_p_16_ nat zero succ even);
  set t0 ≔ (def_unfold_t0_ nat zero succ even a0 a1);
  set t1_a0 ≔ (def_unfold_t1_a0_ nat zero succ even a0 a1);
  set t1_t0 ≔ (def_unfold_t1_t0_ nat zero succ even a0 a1);
  set t1_t1 ≔ (def_unfold_t1_t1_ nat zero succ even a0 a1);
  set t1_t2 ≔ (def_unfold_t1_t2_ nat zero succ even a0 a1);
  set t1_t3 ≔ (def_unfold_t1_t3_ nat zero succ even a0 a1);
  set t1_t4 ≔ (def_unfold_t1_t4_ nat zero succ even a0 a1);
  set t1_t5 ≔ (def_unfold_t1_t5_ nat zero succ even a0 a1);
  set t1 ≔ (def_unfold_t1_ nat zero succ even a0 a1);
  set t2 ≔ (def_unfold_t2_ nat zero succ even a0 a1);
  set t3 ≔ (def_unfold_t3_ nat zero succ even a0 a1);
  set t4 ≔ (def_unfold_t4_ nat zero succ even a0 a1);
  set t5 ≔ (def_unfold_t5_ nat zero succ even a0 a1);
  set t6 ≔ (def_unfold_t6_ nat zero succ even a0 a1);
  set t7 ≔ (def_unfold_t7_ nat zero succ even a0 a1);
  assume hGoal;
  refine (disj_resolutionN1 (p_16 ⸬ p_8 ⸬ □) (p_1 ⸬ □) Stdlib.Nat.1
          Stdlib.Nat.0
          (disj_resolutionN2 (p_16 ⸬ p_8 ⸬ p_5 ⸬ □) (p_6 ⸬ □)
           Stdlib.Nat.2 Stdlib.Nat.0 t7 hGoal ⊤ᵢ ⊤ᵢ (eq_refl _))
          a0 ⊤ᵢ ⊤ᵢ (eq_refl _))
    ;
end;
opaque symbol def_unfold_t10_ (nat : Set) (zero : (τ (nat)))
  (succ : (τ (nat ⤳ nat))) (even : (τ (nat ⤳ o)))
  (a0 : π̇ ((def_unfold_p_1_ nat zero succ even) ⸬ □))
  (a1 : π̇ ((def_unfold_p_2_ nat zero succ even) ⸬ □))
  : π̇
    ((def_unfold_p_14_ nat zero succ even) ⸬ (def_unfold_p_15_ nat zero succ even) ⸬
     (def_unfold_p_7_ nat zero succ even) ⸬ □)
  ≔
begin
assume nat zero succ even a0 a1;
  set p_1 ≔ (def_unfold_p_1_ nat zero succ even);
  set p_2 ≔ (def_unfold_p_2_ nat zero succ even);
  set p_3 ≔ (def_unfold_p_3_ nat zero succ even);
  set p_4 ≔ (def_unfold_p_4_ nat zero succ even);
  set p_5 ≔ (def_unfold_p_5_ nat zero succ even);
  set p_6 ≔ (def_unfold_p_6_ nat zero succ even);
  set p_7 ≔ (def_unfold_p_7_ nat zero succ even);
  set p_8 ≔ (def_unfold_p_8_ nat zero succ even);
  set p_9 ≔ (def_unfold_p_9_ nat zero succ even);
  set p_10 ≔ (def_unfold_p_10_ nat zero succ even);
  set p_11 ≔ (def_unfold_p_11_ nat zero succ even);
  set p_12 ≔ (def_unfold_p_12_ nat zero succ even);
  set p_13 ≔ (def_unfold_p_13_ nat zero succ even);
  set p_14 ≔ (def_unfold_p_14_ nat zero succ even);
  set p_15 ≔ (def_unfold_p_15_ nat zero succ even);
  set p_16 ≔ (def_unfold_p_16_ nat zero succ even);
  set t0 ≔ (def_unfold_t0_ nat zero succ even a0 a1);
  set t1_a0 ≔ (def_unfold_t1_a0_ nat zero succ even a0 a1);
  set t1_t0 ≔ (def_unfold_t1_t0_ nat zero succ even a0 a1);
  set t1_t1 ≔ (def_unfold_t1_t1_ nat zero succ even a0 a1);
  set t1_t2 ≔ (def_unfold_t1_t2_ nat zero succ even a0 a1);
  set t1_t3 ≔ (def_unfold_t1_t3_ nat zero succ even a0 a1);
  set t1_t4 ≔ (def_unfold_t1_t4_ nat zero succ even a0 a1);
  set t1_t5 ≔ (def_unfold_t1_t5_ nat zero succ even a0 a1);
  set t1 ≔ (def_unfold_t1_ nat zero succ even a0 a1);
  set t2 ≔ (def_unfold_t2_ nat zero succ even a0 a1);
  set t3 ≔ (def_unfold_t3_ nat zero succ even a0 a1);
  set t4 ≔ (def_unfold_t4_ nat zero succ even a0 a1);
  set t5 ≔ (def_unfold_t5_ nat zero succ even a0 a1);
  set t6 ≔ (def_unfold_t6_ nat zero succ even a0 a1);
  set t7 ≔ (def_unfold_t7_ nat zero succ even a0 a1);
  set t9 ≔ (def_unfold_t9_ nat zero succ even a0 a1);
  apply (equiv_pos2);
end;
opaque symbol def_unfold_t11_ (nat : Set) (zero : (τ (nat)))
  (succ : (τ (nat ⤳ nat))) (even : (τ (nat ⤳ o)))
  (a0 : π̇ ((def_unfold_p_1_ nat zero succ even) ⸬ □))
  (a1 : π̇ ((def_unfold_p_2_ nat zero succ even) ⸬ □))
  : π̇ ((def_unfold_p_13_ nat zero succ even) ⸬ □) ≔
begin
assume nat zero succ even a0 a1;
  set p_1 ≔ (def_unfold_p_1_ nat zero succ even);
  set p_2 ≔ (def_unfold_p_2_ nat zero succ even);
  set p_3 ≔ (def_unfold_p_3_ nat zero succ even);
  set p_4 ≔ (def_unfold_p_4_ nat zero succ even);
  set p_5 ≔ (def_unfold_p_5_ nat zero succ even);
  set p_6 ≔ (def_unfold_p_6_ nat zero succ even);
  set p_7 ≔ (def_unfold_p_7_ nat zero succ even);
  set p_8 ≔ (def_unfold_p_8_ nat zero succ even);
  set p_9 ≔ (def_unfold_p_9_ nat zero succ even);
  set p_10 ≔ (def_unfold_p_10_ nat zero succ even);
  set p_11 ≔ (def_unfold_p_11_ nat zero succ even);
  set p_12 ≔ (def_unfold_p_12_ nat zero succ even);
  set p_13 ≔ (def_unfold_p_13_ nat zero succ even);
  set p_14 ≔ (def_unfold_p_14_ nat zero succ even);
  set p_15 ≔ (def_unfold_p_15_ nat zero succ even);
  set p_16 ≔ (def_unfold_p_16_ nat zero succ even);
  set t0 ≔ (def_unfold_t0_ nat zero succ even a0 a1);
  set t1_a0 ≔ (def_unfold_t1_a0_ nat zero succ even a0 a1);
  set t1_t0 ≔ (def_unfold_t1_t0_ nat zero succ even a0 a1);
  set t1_t1 ≔ (def_unfold_t1_t1_ nat zero succ even a0 a1);
  set t1_t2 ≔ (def_unfold_t1_t2_ nat zero succ even a0 a1);
  set t1_t3 ≔ (def_unfold_t1_t3_ nat zero succ even a0 a1);
  set t1_t4 ≔ (def_unfold_t1_t4_ nat zero succ even a0 a1);
  set t1_t5 ≔ (def_unfold_t1_t5_ nat zero succ even a0 a1);
  set t1 ≔ (def_unfold_t1_ nat zero succ even a0 a1);
  set t2 ≔ (def_unfold_t2_ nat zero succ even a0 a1);
  set t3 ≔ (def_unfold_t3_ nat zero succ even a0 a1);
  set t4 ≔ (def_unfold_t4_ nat zero succ even a0 a1);
  set t5 ≔ (def_unfold_t5_ nat zero succ even a0 a1);
  set t6 ≔ (def_unfold_t6_ nat zero succ even a0 a1);
  set t7 ≔ (def_unfold_t7_ nat zero succ even a0 a1);
  set t9 ≔ (def_unfold_t9_ nat zero succ even a0 a1);
  set t10 ≔ (def_unfold_t10_ nat zero succ even a0 a1);
  apply ∨ᵢ₁;
  apply bind_∀;
  assume n;
  have t11_t0: π̇
               (((((even n)) ⇒ ((even (succ (succ n))))) =
                 ((¬ ((even n))) ∨ (even (succ (succ n)))))
                ⸬ □)
    { apply ∨ᵢ₁; rewrite bool-impl-elim; reflexivity; };
  apply (π̇ₗ t11_t0);
end;
opaque symbol def_unfold_t12_ (nat : Set) (zero : (τ (nat)))
  (succ : (τ (nat ⤳ nat))) (even : (τ (nat ⤳ o)))
  (a0 : π̇ ((def_unfold_p_1_ nat zero succ even) ⸬ □))
  (a1 : π̇ ((def_unfold_p_2_ nat zero succ even) ⸬ □))
  : π̇ ((def_unfold_p_7_ nat zero succ even) ⸬ □) ≔
begin
assume nat zero succ even a0 a1;
  set p_1 ≔ (def_unfold_p_1_ nat zero succ even);
  set p_2 ≔ (def_unfold_p_2_ nat zero succ even);
  set p_3 ≔ (def_unfold_p_3_ nat zero succ even);
  set p_4 ≔ (def_unfold_p_4_ nat zero succ even);
  set p_5 ≔ (def_unfold_p_5_ nat zero succ even);
  set p_6 ≔ (def_unfold_p_6_ nat zero succ even);
  set p_7 ≔ (def_unfold_p_7_ nat zero succ even);
  set p_8 ≔ (def_unfold_p_8_ nat zero succ even);
  set p_9 ≔ (def_unfold_p_9_ nat zero succ even);
  set p_10 ≔ (def_unfold_p_10_ nat zero succ even);
  set p_11 ≔ (def_unfold_p_11_ nat zero succ even);
  set p_12 ≔ (def_unfold_p_12_ nat zero succ even);
  set p_13 ≔ (def_unfold_p_13_ nat zero succ even);
  set p_14 ≔ (def_unfold_p_14_ nat zero succ even);
  set p_15 ≔ (def_unfold_p_15_ nat zero succ even);
  set p_16 ≔ (def_unfold_p_16_ nat zero succ even);
  set t0 ≔ (def_unfold_t0_ nat zero succ even a0 a1);
  set t1_a0 ≔ (def_unfold_t1_a0_ nat zero succ even a0 a1);
  set t1_t0 ≔ (def_unfold_t1_t0_ nat zero succ even a0 a1);
  set t1_t1 ≔ (def_unfold_t1_t1_ nat zero succ even a0 a1);
  set t1_t2 ≔ (def_unfold_t1_t2_ nat zero succ even a0 a1);
  set t1_t3 ≔ (def_unfold_t1_t3_ nat zero succ even a0 a1);
  set t1_t4 ≔ (def_unfold_t1_t4_ nat zero succ even a0 a1);
  set t1_t5 ≔ (def_unfold_t1_t5_ nat zero succ even a0 a1);
  set t1 ≔ (def_unfold_t1_ nat zero succ even a0 a1);
  set t2 ≔ (def_unfold_t2_ nat zero succ even a0 a1);
  set t3 ≔ (def_unfold_t3_ nat zero succ even a0 a1);
  set t4 ≔ (def_unfold_t4_ nat zero succ even a0 a1);
  set t5 ≔ (def_unfold_t5_ nat zero succ even a0 a1);
  set t6 ≔ (def_unfold_t6_ nat zero succ even a0 a1);
  set t7 ≔ (def_unfold_t7_ nat zero succ even a0 a1);
  set t9 ≔ (def_unfold_t9_ nat zero succ even a0 a1);
  set t10 ≔ (def_unfold_t10_ nat zero succ even a0 a1);
  set t11 ≔ (def_unfold_t11_ nat zero succ even a0 a1);
  refine (disj_resolutionN1 (p_15 ⸬ p_7 ⸬ □) (p_2 ⸬ □) Stdlib.Nat.0
          Stdlib.Nat.0
          (disj_resolutionN1 (p_14 ⸬ p_15 ⸬ p_7 ⸬ □) (p_13 ⸬ □)
           Stdlib.Nat.0 Stdlib.Nat.0 t10 t11 ⊤ᵢ ⊤ᵢ (eq_refl _))
          a1 ⊤ᵢ ⊤ᵢ (eq_refl _))
    ;
end;
opaque symbol def_unfold_t13_ (nat : Set) (zero : (τ (nat)))
  (succ : (τ (nat ⤳ nat))) (even : (τ (nat ⤳ o)))
  (a0 : π̇ ((def_unfold_p_1_ nat zero succ even) ⸬ □))
  (a1 : π̇ ((def_unfold_p_2_ nat zero succ even) ⸬ □))
  (hGoal : π̇ ((def_unfold_p_6_ nat zero succ even) ⸬ □)) : π̇ □ ≔
begin
assume nat zero succ even a0 a1;
  set p_1 ≔ (def_unfold_p_1_ nat zero succ even);
  set p_2 ≔ (def_unfold_p_2_ nat zero succ even);
  set p_3 ≔ (def_unfold_p_3_ nat zero succ even);
  set p_4 ≔ (def_unfold_p_4_ nat zero succ even);
  set p_5 ≔ (def_unfold_p_5_ nat zero succ even);
  set p_6 ≔ (def_unfold_p_6_ nat zero succ even);
  set p_7 ≔ (def_unfold_p_7_ nat zero succ even);
  set p_8 ≔ (def_unfold_p_8_ nat zero succ even);
  set p_9 ≔ (def_unfold_p_9_ nat zero succ even);
  set p_10 ≔ (def_unfold_p_10_ nat zero succ even);
  set p_11 ≔ (def_unfold_p_11_ nat zero succ even);
  set p_12 ≔ (def_unfold_p_12_ nat zero succ even);
  set p_13 ≔ (def_unfold_p_13_ nat zero succ even);
  set p_14 ≔ (def_unfold_p_14_ nat zero succ even);
  set p_15 ≔ (def_unfold_p_15_ nat zero succ even);
  set p_16 ≔ (def_unfold_p_16_ nat zero succ even);
  set t0 ≔ (def_unfold_t0_ nat zero succ even a0 a1);
  set t1_a0 ≔ (def_unfold_t1_a0_ nat zero succ even a0 a1);
  set t1_t0 ≔ (def_unfold_t1_t0_ nat zero succ even a0 a1);
  set t1_t1 ≔ (def_unfold_t1_t1_ nat zero succ even a0 a1);
  set t1_t2 ≔ (def_unfold_t1_t2_ nat zero succ even a0 a1);
  set t1_t3 ≔ (def_unfold_t1_t3_ nat zero succ even a0 a1);
  set t1_t4 ≔ (def_unfold_t1_t4_ nat zero succ even a0 a1);
  set t1_t5 ≔ (def_unfold_t1_t5_ nat zero succ even a0 a1);
  set t1 ≔ (def_unfold_t1_ nat zero succ even a0 a1);
  set t2 ≔ (def_unfold_t2_ nat zero succ even a0 a1);
  set t3 ≔ (def_unfold_t3_ nat zero succ even a0 a1);
  set t4 ≔ (def_unfold_t4_ nat zero succ even a0 a1);
  set t5 ≔ (def_unfold_t5_ nat zero succ even a0 a1);
  set t6 ≔ (def_unfold_t6_ nat zero succ even a0 a1);
  set t7 ≔ (def_unfold_t7_ nat zero succ even a0 a1);
  set t9 ≔ (def_unfold_t9_ nat zero succ even a0 a1);
  set t10 ≔ (def_unfold_t10_ nat zero succ even a0 a1);
  set t11 ≔ (def_unfold_t11_ nat zero succ even a0 a1);
  set t12 ≔ (def_unfold_t12_ nat zero succ even a0 a1);
  assume hGoal;
  refine (disj_resolutionN1 (p_11 ⸬ □) (p_7 ⸬ □) Stdlib.Nat.0
          Stdlib.Nat.0
          (disj_resolutionN2 (p_11 ⸬ p_9 ⸬ □) (p_16 ⸬ □)
           Stdlib.Nat.1 Stdlib.Nat.0 t6 (t9 hGoal) ⊤ᵢ ⊤ᵢ (eq_refl _))
          t12 ⊤ᵢ ⊤ᵢ (eq_refl _))
    ;
end;
opaque symbol def_unfold_a2_ (nat : Set) (zero : (τ (nat))) (succ : (τ (nat ⤳ nat)))
  (even : (τ (nat ⤳ o))) (a0 : π̇ ((def_unfold_p_1_ nat zero succ even) ⸬ □))
  (a1 : π̇ ((def_unfold_p_2_ nat zero succ even) ⸬ □))
  : π (def_unfold_p_5_ nat zero succ even) ≔
begin
assume nat zero succ even a0 a1;
  set p_1 ≔ (def_unfold_p_1_ nat zero succ even);
  set p_2 ≔ (def_unfold_p_2_ nat zero succ even);
  set p_3 ≔ (def_unfold_p_3_ nat zero succ even);
  set p_4 ≔ (def_unfold_p_4_ nat zero succ even);
  set p_5 ≔ (def_unfold_p_5_ nat zero succ even);
  set p_6 ≔ (def_unfold_p_6_ nat zero succ even);
  set p_7 ≔ (def_unfold_p_7_ nat zero succ even);
  set p_8 ≔ (def_unfold_p_8_ nat zero succ even);
  set p_9 ≔ (def_unfold_p_9_ nat zero succ even);
  set p_10 ≔ (def_unfold_p_10_ nat zero succ even);
  set p_11 ≔ (def_unfold_p_11_ nat zero succ even);
  set p_12 ≔ (def_unfold_p_12_ nat zero succ even);
  set p_13 ≔ (def_unfold_p_13_ nat zero succ even);
  set p_14 ≔ (def_unfold_p_14_ nat zero succ even);
  set p_15 ≔ (def_unfold_p_15_ nat zero succ even);
  set p_16 ≔ (def_unfold_p_16_ nat zero succ even);
  set t0 ≔ (def_unfold_t0_ nat zero succ even a0 a1);
  set t1_a0 ≔ (def_unfold_t1_a0_ nat zero succ even a0 a1);
  set t1_t0 ≔ (def_unfold_t1_t0_ nat zero succ even a0 a1);
  set t1_t1 ≔ (def_unfold_t1_t1_ nat zero succ even a0 a1);
  set t1_t2 ≔ (def_unfold_t1_t2_ nat zero succ even a0 a1);
  set t1_t3 ≔ (def_unfold_t1_t3_ nat zero succ even a0 a1);
  set t1_t4 ≔ (def_unfold_t1_t4_ nat zero succ even a0 a1);
  set t1_t5 ≔ (def_unfold_t1_t5_ nat zero succ even a0 a1);
  set t1 ≔ (def_unfold_t1_ nat zero succ even a0 a1);
  set t2 ≔ (def_unfold_t2_ nat zero succ even a0 a1);
  set t3 ≔ (def_unfold_t3_ nat zero succ even a0 a1);
  set t4 ≔ (def_unfold_t4_ nat zero succ even a0 a1);
  set t5 ≔ (def_unfold_t5_ nat zero succ even a0 a1);
  set t6 ≔ (def_unfold_t6_ nat zero succ even a0 a1);
  set t7 ≔ (def_unfold_t7_ nat zero succ even a0 a1);
  set t9 ≔ (def_unfold_t9_ nat zero succ even a0 a1);
  set t10 ≔ (def_unfold_t10_ nat zero succ even a0 a1);
  set t11 ≔ (def_unfold_t11_ nat zero succ even a0 a1);
  set t12 ≔ (def_unfold_t12_ nat zero succ even a0 a1);
  set t13 ≔ (def_unfold_t13_ nat zero succ even a0 a1);
  apply contradiction;
  assume hGoal;
  refine (t13 (clᵢ₁' hGoal));
end;

opaque symbol def_unfold :
  π (`∀ n, even n ⇒ even (succ (succ n))) → π (even zero) → π (even two) ≔
begin
  simplify two;
  assume h0 h1;
  refine
    (λ (nat' : Set)
        (zero' : τ (nat'))
        (succ' : τ ((nat') Stdlib.HOL.⤳ (nat')))
        (even' : τ ((nat') Stdlib.HOL.⤳ Stdlib.Impred.o))
        (a0 : alethe.core.π̇ ((def_unfold_p_1_ (nat') (zero') (succ') (even')) Stdlib.List.⸬ (Stdlib.List.□)))
        (a1 : alethe.core.π̇ ((def_unfold_p_2_ (nat') (zero') (succ') (even')) Stdlib.List.⸬ (Stdlib.List.□)))
        (goal : (π (def_unfold_p_5_ (nat') (zero') (succ') (even'))) → π (even (succ (succ zero)))),
        goal (def_unfold_a2_ nat' zero' succ' even' a0 a1))
    _ _ _ _ _ _ _
    { admit } { admit } { admit } { admit } { admit } { admit } { admit };
end;

// ==========================================================================
// Generated code for opaque_atom: the opaque_atom_* symbols below and its proof.
// ==========================================================================
symbol opaque_atom_p_1_ (X : (τ (o))) ≔ (¬ (X));
opaque symbol opaque_atom_t0_ (X : (τ (o))) (a0 : π̇ (X ⸬ □))
  (hGoal : π̇ ((opaque_atom_p_1_ X) ⸬ □)) : π̇ □ ≔
begin
assume X a0;
  set p_1 ≔ (opaque_atom_p_1_ X);
  assume hGoal;
  refine (disj_resolutionN2 (X ⸬ □) (p_1 ⸬ □) Stdlib.Nat.0
          Stdlib.Nat.0 a0 hGoal ⊤ᵢ ⊤ᵢ (eq_refl _))
    ;
end;
opaque symbol opaque_atom_a1_ (X : (τ (o))) (a0 : π̇ (X ⸬ □)) : π X ≔
begin
assume X a0;
  set p_1 ≔ (opaque_atom_p_1_ X);
  set t0 ≔ (opaque_atom_t0_ X a0);
  apply contradiction;
  assume hGoal;
  refine (t0 (clᵢ₁' hGoal));
end;

opaque symbol opaque_atom :
  π (P (λ x, even (plus zero x))) → π (P (λ x, even x)) ≔
begin
  assume h0;
  refine
    (λ (X' : τ Stdlib.Impred.o)
        (a0 : alethe.core.π̇ ((X') Stdlib.List.⸬ (Stdlib.List.□)))
        (goal : (π (X')) → π (P (λ x, even x))),
        goal (opaque_atom_a1_ X' a0))
    _ _ _
    { admit } { admit } { admit };
end;

// ==========================================================================
// Generated code for empty_type: the empty_type_* symbols below and its proof.
// ==========================================================================
symbol empty_type_p_1 ≔ (¬ (⊤));
symbol empty_type_p_2 ≔ (empty_type_p_1 = ⊥);
symbol empty_type_p_3 ≔ (¬ (empty_type_p_2));
symbol empty_type_p_4 ≔ (¬ (empty_type_p_1));
symbol empty_type_p_5 ≔ (¬ (⊥));
opaque symbol empty_type_t0 : π̇ (empty_type_p_3 ⸬ empty_type_p_4 ⸬ ⊥ ⸬ □) ≔
begin
apply (equiv_pos2);
end;
opaque symbol empty_type_t1 : π̇ (empty_type_p_2 ⸬ □) ≔
begin
apply ∨ᵢ₁; simplify empty_type_p_2; simplify empty_type_p_1; refine ¬⊤;
end;
opaque symbol empty_type_t2 (hGoal : π̇ (empty_type_p_1 ⸬ □)) : π̇ (⊥ ⸬ □) ≔
begin
assume hGoal;
  refine (disj_resolutionN1 (empty_type_p_4 ⸬ ⊥ ⸬ □) (empty_type_p_1 ⸬ □) Stdlib.Nat.0
          Stdlib.Nat.0
          (disj_resolutionN1 (empty_type_p_3 ⸬ empty_type_p_4 ⸬ ⊥ ⸬ □) (empty_type_p_2 ⸬ □)
           Stdlib.Nat.0 Stdlib.Nat.0 empty_type_t0 empty_type_t1 ⊤ᵢ ⊤ᵢ (eq_refl _))
          hGoal ⊤ᵢ ⊤ᵢ (eq_refl _))
    ;
end;
opaque symbol empty_type_t3 : π̇ (empty_type_p_5 ⸬ □) ≔
begin
apply ∨ᵢ₁; refine neg_⊥;
end;
opaque symbol empty_type_t4 (hGoal : π̇ (empty_type_p_1 ⸬ □)) : π̇ □ ≔
begin
assume hGoal;
  refine (disj_resolutionN2 (⊥ ⸬ □) (empty_type_p_5 ⸬ □) Stdlib.Nat.0
          Stdlib.Nat.0 (empty_type_t2 hGoal) empty_type_t3 ⊤ᵢ ⊤ᵢ (eq_refl _))
    ;
end;
opaque symbol empty_type_a0 : π ⊤ ≔
begin
apply contradiction; assume hGoal; refine (empty_type_t4 (clᵢ₁' hGoal));
end;

opaque symbol empty_type : π (`∃ n, even n ⇒ even n) ≔
begin
  refine
    (λ (goal : (π ⊤) → π (`∃ n, (even n) ⇒ (even n))),
        goal (empty_type_a0))
    _;
  admit;
end;

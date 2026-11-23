// What the why3 tactic does to the goal before CVC5 sees it, and what that
// leaves to the reconstruction. See README.md.
require open Stdlib.Set Stdlib.Prop Stdlib.FOL;
require alethe.core alethe.prop alethe.rare.prop alethe.quant;

prover "CVC5";
prover_timeout 10;

constant symbol nat : Set;
constant symbol zero : τ nat;
constant symbol succ : τ nat → τ nat;
symbol even : τ nat → Prop;

symbol plus : τ nat → τ nat → τ nat;
rule plus zero $n ↪ $n;

symbol two ≔ succ (succ zero);

symbol P : (τ nat → Prop) → Prop;

// Rewrite rules and definitions are not sent to Why3: unfold them first.
opaque symbol rule_unfold : π (even zero) → π (even (plus zero zero)) ≔
begin simplify plus; why3 end;

opaque symbol def_unfold :
  π (`∀ n, even n ⇒ even (succ (succ n))) → π (even zero) → π (even two) ≔
begin simplify two; why3 end;

// P is higher-order, so both formulas become the same opaque atom X (they
// are convertible). X is a constant of the problem that no variable of the
// goal stands for: a hole of type Prop.
opaque symbol opaque_atom :
  π (P (λ x, even (plus zero x))) → π (P (λ x, even x)) ≔
begin why3 end;

// cvc5.drv simplifies the goal to true (A ⇒ A → ⊤, then the unused ∃ is
// dropped), so the theorem is π ⊤. The remaining hole π ⊤ → π G needs an
// element of τ nat, which is not provable in general (empty types).
opaque symbol empty_type : π (`∃ n, even n ⇒ even n) ≔
begin why3 end;

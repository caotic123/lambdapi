// Precise characterization of hypothesis-reflection with the current machinery.
symbol U : TYPE; injective symbol El : U → TYPE;
symbol Eq : Π (a : U), El a → El a → TYPE;
when Eq $e : Eq $a $x $y
   ⊢ $x ≡ $y;                             // reflection: proof ⇒ equation
symbol A : U; symbol t : El A; symbol u : El A;
symbol v : El A; symbol w : El A;
// (i) LOCAL hypothesis: does NOT fire (context vars are not saturated) —
//     incomplete but SAFE.  And crucially, NO LEAK once the binder closes:
symbol tryLocal : Π (e : Eq A t u), El A ≔ λ e, t;    // e unused: types fine
assertnot ⊢ t ≡ u;                        // must hold: nothing leaked
// (ii) GLOBAL axiom: fires at its declaration's flush — and that IS sound
//      (an axiom's equation holds unconditionally):
symbol ax : Eq A v w;
assert ⊢ v ≡ w;                           // reflected from the axiom
assertnot ⊢ t ≡ u;                        // still no contamination of t, u

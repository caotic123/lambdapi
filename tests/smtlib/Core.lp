// Library required by the proofs reconstructed from SMT solvers (see
// src/handle/reconstruct.ml). Adapted step by step from the core of
// Alessio Coltellacci's Alethe library (carcara, branch lambdapi-refactor,
// alethe-lp/core.lp), over tests.OK instead of Stdlib.
//
// No classical axiom is declared here. A lemma that needs excluded middle
// on a proposition p takes a proof of p ∨ ¬ p as its first premise.
//
// Moved so far: the clause type and its introduction and elimination
// rules, and the classical relations between ¬, ∨ and ⇒.
//
// tests.OK.PropExt is not required: it requires tests.OK.Classic, which
// declares em. Equations between propositions of core.lp are therefore
// stated as implications.
require open tests.OK.Set tests.OK.Prop tests.OK.FOL tests.OK.Eq
  tests.OK.Impred tests.OK.Nat tests.OK.List;

// testing symbols
private symbol a : Prop;
private symbol b : Prop;
private symbol c : Prop;

// ---------------------------------------------------------------------------
// Clauses.
//
// A clause is a list of propositions, with □ for the empty clause and ⸬ for
// the literal cons. disj reads it back as a disjunction, and π̇ l is the
// judgement "the clause l holds".

symbol disj : 𝕃 o → Prop;
rule disj ($l1 ⸬ $l) ↪ ($l1 ∨ disj $l)
with disj □ ↪ ⊥;

assert ⊢ disj (a ⸬ b ⸬ □) ≡ a ∨ b ∨ ⊥;

injective symbol π̇ (l : 𝕃 o) : TYPE ≔ π (disj l);

builtin "smt_disj" ≔ disj;
builtin "smt_clause" ≔ π̇;

// disj (l ++ l') = (disj l ∨ disj l')
opaque symbol disj_cat (l l' : 𝕃 o) : π (disj (l ++ l')) → π (disj l ∨ disj l') ≔
begin
  induction
  { assume l' h; apply ∨ᵢ₂; apply h }
  { assume l0 l ih l' h;
    apply ∨ₑ h
    { assume h0; apply ∨ᵢ₁; apply ∨ᵢ₁; apply h0 }
    { assume h1;
      apply ∨ₑ (ih l' h1)
      { assume hl; apply ∨ᵢ₁; apply ∨ᵢ₂; apply hl }
      { assume hl'; apply ∨ᵢ₂; apply hl' } } }
end;

opaque symbol disj_cat_inv (l l' : 𝕃 o) : π (disj l ∨ disj l') → π (disj (l ++ l')) ≔
begin
  induction
  { assume l' h;
    apply ∨ₑ h
    { assume hbot; apply ⊥ₑ; apply hbot }
    { assume hl'; apply hl' } }
  { assume l0 l ih l' h;
    apply ∨ₑ h
    { assume hl;
      apply ∨ₑ hl
      { assume h0; apply ∨ᵢ₁; apply h0 }
      { assume h1; apply ∨ᵢ₂; apply ih l'; apply ∨ᵢ₁; apply h1 } }
    { assume hl'; apply ∨ᵢ₂; apply ih l'; apply ∨ᵢ₂; apply hl' } }
end;

// Flattens an ∨-chain into the clause it denotes. Used by the `or` rule.
sequential symbol ∨_to_list : Prop → 𝕃 o;
rule ∨_to_list ($x ∨ $y) ↪ $x ⸬ (∨_to_list $y)
with ∨_to_list ⊥ ↪ □;

assert ⊢ ∨_to_list (a ∨ b ∨ ⊥ ∨ c ∨ ⊥) ≡ (a ⸬ b ⸬ ⊥ ⸬ c ⸬ □);

// From the unit clause to its literal.
opaque symbol π̇ₗ [a] : π̇ (a ⸬ □) → π a ≔
begin
  assume a Hcl_a;
  apply @∨ₑ a ⊥ a
  { apply Hcl_a }
  { assume Ha; apply Ha }
  { assume False; apply ⊥ₑ False }
end;

// Introduction rules for clauses.
opaque symbol clᵢ₁ [p q] : π̇ (p ⸬ □) → π̇ (p ⸬ q) ≔
begin
  assume p q Hp;
  apply ∨ₑ Hp
  { assume Hpi_p; apply ∨ᵢ₁; apply Hpi_p }
  { assume Hbot; apply ⊥ₑ; apply Hbot }
end;

opaque symbol clᵢ₁' [p q] : π p → π̇ (p ⸬ q) ≔
begin
  assume p q Hp; apply ∨ᵢ₁; apply Hp
end;

opaque symbol clᵢ₂ [p q] : π̇ q → π̇ (p ⸬ q) ≔
begin
  assume p q Hq; apply ∨ᵢ₂; apply Hq
end;

// Elimination rule for clauses.
opaque symbol clₑ [p q r] :
  π̇ (p ⸬ q) → (π̇ (p ⸬ □) → π̇ r) → (π̇ q → π̇ r) → π̇ r ≔
begin
  assume p q r Hpq Hpr Hqr;
  apply ∨ₑ Hpq
  { assume Hp; apply Hpr (∨ᵢ₁ Hp) }
  { assume Hq; apply Hqr Hq }
end;

// ---------------------------------------------------------------------------
// Classical relations. core.lp states them as equations proved with the
// axioms em and prop_ext (nnpp_eq, imp_eq_or). Here each direction is a
// lemma, and the classical one takes the excluded middle instance it needs
// as its first premise.

// ¬ ¬ p = p
opaque symbol nnpp [p] : π (p ∨ ¬ p) → π (¬ ¬ p) → π p ≔
begin
  assume p em nnp;
  apply ∨ₑ em
  { assume h; apply h }
  { assume np; apply ⊥ₑ; apply nnp np }
end;

opaque symbol nnpp_inv [p] : π p → π (¬ ¬ p) ≔
begin
  assume p h np; apply np h
end;

// (¬ p ∨ q) = (p ⇒ q)
opaque symbol or_imp [p q] : π (¬ p ∨ q) → π (p ⇒ q) ≔
begin
  assume p q h hp;
  apply ∨ₑ h
  { assume np; apply ⊥ₑ; apply np hp }
  { assume hq; apply hq }
end;

opaque symbol imp_or [p q] : π (p ∨ ¬ p) → π (p ⇒ q) → π (¬ p ∨ q) ≔
begin
  assume p q em h;
  apply ∨ₑ em
  { assume hp; apply ∨ᵢ₂; apply h hp }
  { assume np; apply ∨ᵢ₁; refine np }
end;

// ---------------------------------------------------------------------------
// Excluded middle is preserved by the connectives. The reconstruction
// builds the instance it needs for a formula from the instances for its
// atoms, so that the user is only asked for the atoms.

opaque symbol em_top : π (⊤ ∨ ¬ ⊤) ≔
begin
  apply ∨ᵢ₁; apply ⊤ᵢ
end;

opaque symbol em_bot : π (⊥ ∨ ¬ ⊥) ≔
begin
  apply ∨ᵢ₂; assume h; apply h
end;

opaque symbol em_not [p] : π (p ∨ ¬ p) → π (¬ p ∨ ¬ ¬ p) ≔
begin
  assume p em;
  apply ∨ₑ em
  { assume h; apply ∨ᵢ₂; assume np; apply np h }
  { assume np; apply ∨ᵢ₁; refine np }
end;

opaque symbol em_and [p q] :
  π (p ∨ ¬ p) → π (q ∨ ¬ q) → π ((p ∧ q) ∨ ¬ (p ∧ q)) ≔
begin
  assume p q ep eq;
  apply ∨ₑ ep
  { assume hp;
    apply ∨ₑ eq
    { assume hq; apply ∨ᵢ₁; apply ∧ᵢ hp hq }
    { assume nq; apply ∨ᵢ₂; assume h; apply nq (∧ₑ₂ h) } }
  { assume np; apply ∨ᵢ₂; assume h; apply np (∧ₑ₁ h) }
end;

opaque symbol em_or [p q] :
  π (p ∨ ¬ p) → π (q ∨ ¬ q) → π ((p ∨ q) ∨ ¬ (p ∨ q)) ≔
begin
  assume p q ep eq;
  apply ∨ₑ ep
  { assume hp; apply ∨ᵢ₁; apply ∨ᵢ₁; apply hp }
  { assume np;
    apply ∨ₑ eq
    { assume hq; apply ∨ᵢ₁; apply ∨ᵢ₂; apply hq }
    { assume nq; apply ∨ᵢ₂; assume h;
      apply ∨ₑ h { assume hp; apply np hp } { assume hq; apply nq hq } } }
end;

opaque symbol em_imp [p q] :
  π (p ∨ ¬ p) → π (q ∨ ¬ q) → π ((p ⇒ q) ∨ ¬ (p ⇒ q)) ≔
begin
  assume p q ep eq;
  apply ∨ₑ eq
  { assume hq; apply ∨ᵢ₁; assume hp; apply hq }
  { assume nq;
    apply ∨ₑ ep
    { assume hp; apply ∨ᵢ₂; assume h; apply nq (h hp) }
    { assume np; apply ∨ᵢ₁; assume hp; apply ⊥ₑ; apply np hp } }
end;

builtin "smt_em_top" ≔ em_top;
builtin "smt_em_bot" ≔ em_bot;
builtin "smt_em_not" ≔ em_not;
builtin "smt_em_and" ≔ em_and;
builtin "smt_em_or" ≔ em_or;
builtin "smt_em_imp" ≔ em_imp;

// ---------------------------------------------------------------------------
// Literals of a clause, by index.

symbol literal ≔ nth ⊥;

builtin "smt_o" ≔ o;
builtin "smt_nil" ≔ □;
builtin "smt_cons" ≔ ⸬;

// A literal implies the disjunction. core.lp proves it through
// lit_imp_disj and or_neg_aux, for an index k in indexes l. No condition
// on k is needed: out of bounds, literal l k is ⊥.
opaque symbol literal_disj (l : 𝕃 o) (k : ℕ) : π (literal l k) → π (disj l) ≔
begin
  induction
  { assume k; refine ind_ℕ (λ k, literal □ k ⇒ disj □) _ _ k
    { assume h; refine h }
    { assume n ih h; refine h } }
  { assume x l ih k;
    refine ind_ℕ (λ k, literal (x ⸬ l) k ⇒ disj (x ⸬ l)) _ _ k
    { assume h; apply ∨ᵢ₁; refine h }
    { assume n ihn h; apply ∨ᵢ₂; refine ih n h } }
end;

// ---------------------------------------------------------------------------
// Rules.

// or_neg: (cl (or φ₁ … φₙ) (not φₖ)) with :args (k), for l = φ₁ ⸬ … ⸬ φₙ ⸬ □.
// core.lp proves ¬φₖ ⸬ c with imp_eq_or. Here the literals are in the
// order of Alethe, and the first premise is excluded middle on φₖ.
opaque symbol or_neg (l : 𝕃 o) (k : ℕ) :
  π (literal l k ∨ ¬ literal l k) → π̇ (disj l ⸬ ¬ literal l k ⸬ □) ≔
begin
  assume l k em;
  apply ∨ₑ em
  { assume h; apply ∨ᵢ₁; refine literal_disj l k h }
  { assume nh; apply ∨ᵢ₂; apply ∨ᵢ₁; refine nh }
end;

builtin "smt_or_neg" ≔ or_neg;

assert ⊢ or_neg (a ⸬ b ⸬ □) 1 :
  π (b ∨ ¬ b) → π ((a ∨ b ∨ ⊥) ∨ ¬ b ∨ ⊥);

// implies: (cl (not φ₁) φ₂) from the premise φ₁ ⇒ φ₂. prop.lp proves it
// with imply_to_or (classical). Here the first premise is excluded middle
// on φ₁.
opaque symbol implies [φ₁ φ₂] :
  π (φ₁ ∨ ¬ φ₁) → π (φ₁ ⇒ φ₂) → π̇ (¬ φ₁ ⸬ φ₂ ⸬ □) ≔
begin
  assume φ₁ φ₂ em h;
  apply ∨ₑ em
  { assume h1; apply ∨ᵢ₂; apply ∨ᵢ₁; refine h h1 }
  { assume n1; apply ∨ᵢ₁; refine n1 }
end;

builtin "smt_implies" ≔ implies;

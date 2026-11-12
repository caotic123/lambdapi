// Alethe rules read in lambdapi without excluded middle, generic in the
// answer r : Prop. Used by replay_examples.lp, which replays by hand the CVC5
// certificates of the coherent-preprocessing test.
//
// Reading (Traversié 2025, Lemma 16, with T r a = (a ⇒ r) ⇒ r):
//   ⟦atom⟧ = atom              ⟦false⟧ = r          ⟦not a⟧ = ⟦a⟧ ⇒ r
//   ⟦a ∧ b⟧, ⟦a ∨ b⟧, ⟦∃x. a⟧  componentwise
//   ⟦a ⇒ b⟧ = ⟦a⟧ ⇒ T r ⟦b⟧    ⟦∀x. a⟧ = ∀x. T r ⟦a⟧
//   ⟦a = b⟧ (Booleans) = Eqv r ⟦a⟧ ⟦b⟧ = (⟦a⟧ ⇒ T r ⟦b⟧) ∧ (⟦b⟧ ⇒ T r ⟦a⟧)
// A clause is read as
//   (cl l₁ … lₙ) = (⟦l₁⟧ ⇒ r) ⇒ … ⇒ (⟦lₙ⟧ ⇒ r) ⇒ r,     (cl) = r.
// So a negative literal (not a) contributes T r ⟦a⟧ ⇒ …, and the unit
// clause (cl a) is T r ⟦a⟧.
//
// No lemma uses ⊥ₑ or a classical axiom, so all hold for every r: r := G
// (Friedman) and r := ⊥ (Glivenko). The T inserted after ⇒ and ∀ is what
// makes implies_neg1, the rewrites and bind provable; with T only at the
// clause level (AGENTS.md) they are not.
//
// Rule table (✓ = lemma below; resolution, contraction, reordering and
// subproof are written inline, see the end of this file):
//   resolution        x ∨ C, ¬x ∨ D ⊢ C ∨ D            inline λ-term      ✓
//   contraction       remove a repeated literal       inline λ-term      ✓
//   reordering        permute the literals            inline λ-term      ✓
//   subproof          discharge an assumption         inline λ           ✓
//   or                (cl (or a b)) ⊢ (cl a b)        or_                ✓
//   or_pos            (cl (not (or a b)) a b)         or_pos             ✓
//   or_neg            (cl (or a b) (not a)), …        or_neg_0, or_neg_1 ✓
//   and_intro         (cl a), (cl b) ⊢ (cl (and a b)) and_intro          ✓
//   implies           (cl (=> a b)) ⊢ (cl (not a) b)  implies            ✓
//   implies_pos       (cl (not (=> a b)) (not a) b)   implies_pos        ✓
//   implies_neg1      (cl (=> a b) a)                 implies_neg1       ✓ needs T after ⇒
//   implies_neg2      (cl (=> a b) (not b))           implies_neg2       ✓
//   forall_inst       (cl (or (not ∀x.φ) φ[t]))       forall_inst        ✓ needs T after ∀
//   equiv_pos2        (cl (not (= a b)) (not a) b)    equiv_pos2         ✓
//   connective_def    ∃x.φ = ¬∀x.¬φ                   connective_def_ex  ✓ needs T after ∀
//   rare_rewrite      bool-impl-elim                  impl_elim          ✓ needs T after ⇒
//                     bool-double-not-elim            double_not_elim    ✓
//                     bool-eq-false                   eq_false           ✓
//   aci_simp          a ∨ b = b ∨ a, false ∨ a = a    or_comm, or_false  ✓
//   miniscope_split   ∀x.(q ∨ φ) = q ∨ ∀x.φ           miniscope_split_or ✓ needs T after ∀
//   refl, symm, trans                                 refl, symm, trans  ✓
//   cong              for not, or, (=> c ·)           cong_not, cong_or, cong_imp_r ✓
//   bind              ∀ congruence                    bind_forall        ✓ needs T after ∀
//   sko_forall        ∀x.ψ = ψ[ε x.¬ψ]                none: ε replaced by the witness of
//                                                     an ∃ hypothesis (sko_forall_witness)
require open tests.OK.Set tests.OK.Prop tests.OK.FOL;

symbol T (r a : Prop) : Prop ≔ (a ⇒ r) ⇒ r;
symbol Eqv (r a b : Prop) : Prop ≔ (a ⇒ T r b) ∧ (b ⇒ T r a);

// An assumption enters as a unit clause.
opaque symbol unit [r a] : π a → π (T r a) ≔ λ h k, k h;

// The negated goal (cl (not G)) is T G G ⇒ G when r := G.
opaque symbol goal [g] : π (T g g ⇒ g) ≔ λ h, h (λ x, x);

// Clausal rules.
opaque symbol or_ [r a b] : π (T r (a ∨ b)) → π ((a ⇒ r) ⇒ (b ⇒ r) ⇒ r) ≔
  λ h ka kb, h (λ o, ∨ₑ o ka kb);
opaque symbol or_pos [r a b] : π (T r (a ∨ b) ⇒ (a ⇒ r) ⇒ (b ⇒ r) ⇒ r) ≔
  λ h ka kb, h (λ o, ∨ₑ o ka kb);
opaque symbol or_neg_0 [r a b] : π (((a ∨ b) ⇒ r) ⇒ T r a ⇒ r) ≔
  λ k h, h (λ x, k (∨ᵢ₁ x));
opaque symbol or_neg_1 [r a b] : π (((a ∨ b) ⇒ r) ⇒ T r b ⇒ r) ≔
  λ k h, h (λ y, k (∨ᵢ₂ y));
opaque symbol and_intro [r a b] : π (T r a) → π (T r b) → π (T r (a ∧ b)) ≔
  λ ha hb k, ha (λ x, hb (λ y, k (∧ᵢ x y)));
opaque symbol implies [r a b] :
  π (T r (a ⇒ T r b)) → π (T r a ⇒ (b ⇒ r) ⇒ r) ≔
  λ h na kb, h (λ f, na (λ x, f x kb));
opaque symbol implies_pos [r a b] :
  π (T r (a ⇒ T r b) ⇒ T r a ⇒ (b ⇒ r) ⇒ r) ≔
  λ h na kb, h (λ f, na (λ x, f x kb));
opaque symbol implies_neg1 [r a b] : π (((a ⇒ T r b) ⇒ r) ⇒ (a ⇒ r) ⇒ r) ≔
  λ k ka, k (λ x _, ka x);
opaque symbol implies_neg2 [r a b] : π (((a ⇒ T r b) ⇒ r) ⇒ T r b ⇒ r) ≔
  λ k hb, k (λ _, hb);
opaque symbol equiv_pos2 [r a b] :
  π (T r (Eqv r a b) ⇒ T r a ⇒ (b ⇒ r) ⇒ r) ≔
  λ h na kb, h (λ e, na (λ x, ∧ₑ₁ e x kb));

// Quantifier instantiation: (cl (or (not (forall x φ)) φ[t])).
opaque symbol forall_inst [r s] (φ : τ s → Prop) (t : τ s) :
  π (T r (((`∀ x, T r (φ x)) ⇒ r) ∨ φ t)) ≔
  λ k, k (∨ᵢ₁ (λ f, f t (λ v, k (∨ᵢ₂ v))));

// Equalities between formulas.
opaque symbol refl [r a] : π (T r (Eqv r a a)) ≔
  λ k, k (∧ᵢ (λ x k', k' x) (λ x k', k' x));
opaque symbol symm [r a b] : π (T r (Eqv r a b)) → π (T r (Eqv r b a)) ≔
  λ h k, h (λ e, k (∧ᵢ (∧ₑ₂ e) (∧ₑ₁ e)));
opaque symbol trans [r a b c] :
  π (T r (Eqv r a b)) → π (T r (Eqv r b c)) → π (T r (Eqv r a c)) ≔
  λ h1 h2 k, h1 (λ e1, h2 (λ e2, k (∧ᵢ
    (λ x k', ∧ₑ₁ e1 x (λ y, ∧ₑ₁ e2 y k'))
    (λ z k', ∧ₑ₂ e2 z (λ y, ∧ₑ₂ e1 y k')))));
opaque symbol cong_not [r a b] :
  π (T r (Eqv r a b)) → π (T r (Eqv r (a ⇒ r) (b ⇒ r))) ≔
  λ h k, h (λ e, k (∧ᵢ
    (λ na k', k' (λ y, ∧ₑ₂ e y na))
    (λ nb k', k' (λ x, ∧ₑ₁ e x nb))));
opaque symbol cong_or [r a b c d] :
  π (T r (Eqv r a b)) → π (T r (Eqv r c d)) →
  π (T r (Eqv r (a ∨ c) (b ∨ d))) ≔
  λ h1 h2 k, h1 (λ e1, h2 (λ e2, k (∧ᵢ
    (λ o k', ∨ₑ o (λ x, ∧ₑ₁ e1 x (λ y, k' (∨ᵢ₁ y)))
                  (λ z, ∧ₑ₁ e2 z (λ w, k' (∨ᵢ₂ w))))
    (λ o k', ∨ₑ o (λ y, ∧ₑ₂ e1 y (λ x, k' (∨ᵢ₁ x)))
                  (λ w, ∧ₑ₂ e2 w (λ z, k' (∨ᵢ₂ z)))))));
opaque symbol cong_imp_r [r c a b] :
  π (T r (Eqv r a b)) → π (T r (Eqv r (c ⇒ T r a) (c ⇒ T r b))) ≔
  λ h k, h (λ e, k (∧ᵢ
    (λ f k', k' (λ z kb, f z (λ v, ∧ₑ₁ e v kb)))
    (λ g k', k' (λ z ka, g z (λ v, ∧ₑ₂ e v ka)))));

// connective_def: (= (exists x φ) (not (forall x (not φ)))).
opaque symbol connective_def_ex [r s] (φ : τ s → Prop) :
  π (T r (Eqv r (`∃ x, φ x) ((`∀ x, T r (φ x ⇒ r)) ⇒ r))) ≔
  λ k, k (∧ᵢ
    (λ e k', ∃ₑ e (λ x px, k' (λ f, f x (λ g, g px))))
    (λ y k', y (λ x h, h (λ px, k' (∃ᵢ x px)))));

// rare_rewrite rules.
opaque symbol impl_elim [r a b] :
  π (T r (Eqv r (a ⇒ T r b) ((a ⇒ r) ∨ b))) ≔
  λ k, k (∧ᵢ
    (λ f k', k' (∨ᵢ₁ (λ x, f x (λ y, k' (∨ᵢ₂ y)))))
    (λ d k', k' (λ x kb, ∨ₑ d (λ na, na x) kb)));
opaque symbol double_not_elim [r a] : π (T r (Eqv r ((a ⇒ r) ⇒ r) a)) ≔
  λ k, k (∧ᵢ (λ h, h) (λ x k', k' (λ k'', k'' x)));
opaque symbol eq_false [r a] : π (T r (Eqv r (Eqv r a r) (a ⇒ r))) ≔
  λ k, k (∧ᵢ
    (λ e k', k' (λ x, ∧ₑ₁ e x (λ y, y)))
    (λ na k', k' (∧ᵢ (λ x _, na x) (λ y _, y))));

// aci_simp instances.
opaque symbol or_comm [r a b] : π (T r (Eqv r (a ∨ b) (b ∨ a))) ≔
  λ k, k (∧ᵢ
    (λ o k', ∨ₑ o (λ x, k' (∨ᵢ₂ x)) (λ y, k' (∨ᵢ₁ y)))
    (λ o k', ∨ₑ o (λ y, k' (∨ᵢ₂ y)) (λ x, k' (∨ᵢ₁ x))));
opaque symbol or_false [r a] : π (T r (Eqv r (r ∨ a) a)) ≔
  λ k, k (∧ᵢ (λ o k', ∨ₑ o (λ y, y) k') (λ x k', k' (∨ᵢ₂ x)));

// miniscope_split: (= (forall x (or q φ)) (or q (forall x φ))), x not in q.
opaque symbol miniscope_split_or [r s] (q : Prop) (φ : τ s → Prop) :
  π (T r (Eqv r (`∀ x, T r (q ∨ φ x)) (q ∨ `∀ x, T r (φ x)))) ≔
  λ k, k (∧ᵢ
    (λ f k', k' (∨ᵢ₂ (λ x k'', f x (λ o, ∨ₑ o (λ y, k' (∨ᵢ₁ y)) k''))))
    (λ o k', k' (λ x k'', ∨ₑ o (λ y, k'' (∨ᵢ₁ y))
                              (λ g, g x (λ v, k'' (∨ᵢ₂ v))))));

// bind for ∀: from the step proved under the binder.
opaque symbol bind_forall [r s] (φ ψ : τ s → Prop) :
  (Π x, π (T r (Eqv r (φ x) (ψ x)))) →
  π (T r (Eqv r (`∀ x, T r (φ x)) (`∀ x, T r (ψ x)))) ≔
  λ h k, k (∧ᵢ
    (λ f k', k' (λ x k'', f x (λ v, h x (λ e, ∧ₑ₁ e v k''))))
    (λ g k', k' (λ x k'', g x (λ v, h x (λ e, ∧ₑ₂ e v k'')))));

// sko_forall (cl (= (forall x (not φ)) (not φ[ε]))) with ε the Skolem
// witness of a hypothesis ∃x. φ: replace ε by the witness w obtained by ∃ₑ.
opaque symbol sko_forall_witness [r s] (φ : τ s → Prop) (w : τ s) :
  π (φ w) → π (T r (Eqv r (`∀ x, T r (φ x ⇒ r)) (φ w ⇒ r))) ≔
  λ pw k, k (∧ᵢ
    (λ f k', f w (λ g, k' g))
    (λ nw _, nw pw));

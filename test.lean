/-!
# Deep embedding of intuitionistic propositional logic

* `Formula α`: propositional formulas over atoms of type `α`, with the
  connectives of SMT-LIB/Alethe (`true`, `false`, `not`, `and`, `or`, `=>`,
  `=` on `Bool`).
* `Γ ⊨ A`: semantic entailment in Kripke models.
* `Γ ⊢[cl] A`: natural deduction in sequent style; `cl = true` adds excluded
  middle. `Γ ⊢ A` is the intuitionistic system, `Γ ⊢ₐ A` the classical one.
* `soundness` and `completeness` relate the two.
-/

namespace IPL

inductive Formula (α : Type) where
  | atom : α → Formula α
  | top  : Formula α
  | bot  : Formula α
  | not  : Formula α → Formula α
  | and  : Formula α → Formula α → Formula α
  | or   : Formula α → Formula α → Formula α
  | imp  : Formula α → Formula α → Formula α
  | iff  : Formula α → Formula α → Formula α
  deriving DecidableEq, Repr

variable {α : Type}

/-! ## Kripke semantics -/

/-- A preorder of worlds with a valuation that is monotone along it. -/
structure KripkeModel (α : Type) where
  World : Type
  le    : World → World → Prop
  refl  : ∀ w, le w w
  trans : ∀ {u v w}, le u v → le v w → le u w
  val   : World → α → Prop
  mono  : ∀ {w w' a}, le w w' → val w a → val w' a

def KripkeModel.Forces (M : KripkeModel α) : M.World → Formula α → Prop
  | w, .atom a  => M.val w a
  | _, .top     => True
  | _, .bot     => False
  | w, .not A   => ∀ w', M.le w w' → ¬ M.Forces w' A
  | w, .and A B => M.Forces w A ∧ M.Forces w B
  | w, .or A B  => M.Forces w A ∨ M.Forces w B
  | w, .imp A B => ∀ w', M.le w w' → M.Forces w' A → M.Forces w' B
  | w, .iff A B => ∀ w', M.le w w' → (M.Forces w' A ↔ M.Forces w' B)

/-- `w` forces every formula of `Γ`. -/
def Satisfies (M : KripkeModel α) (w : M.World) (Γ : List (Formula α)) : Prop :=
  ∀ B ∈ Γ, M.Forces w B

/-- Every world of every Kripke model that forces `Γ` forces `A`. -/
def Entails (Γ : List (Formula α)) (A : Formula α) : Prop :=
  ∀ (M : KripkeModel α) (w : M.World), Satisfies M w Γ → M.Forces w A

scoped infix:25 " ⊨ " => Entails

def Valid (A : Formula α) : Prop := [] ⊨ A

/-- Forcing is preserved when moving to a later world. -/
theorem KripkeModel.Forces.mono {M : KripkeModel α} {w w' : M.World}
    (h : M.le w w') : ∀ {A : Formula α}, M.Forces w A → M.Forces w' A
  | .atom _,  hA => M.mono h hA
  | .top,     _  => trivial
  | .bot,     hA => hA
  | .not _,   hA => fun _ h' => hA _ (M.trans h h')
  | .and _ _, hA => ⟨Forces.mono h hA.1, Forces.mono h hA.2⟩
  | .or _ _,  hA => hA.elim (fun h₁ => .inl (Forces.mono h h₁))
                            (fun h₂ => .inr (Forces.mono h h₂))
  | .imp _ _, hA => fun _ h' => hA _ (M.trans h h')
  | .iff _ _, hA => fun _ h' => hA _ (M.trans h h')

theorem Satisfies.mono {M : KripkeModel α} {w w' : M.World}
    {Γ : List (Formula α)} (h : M.le w w') (hΓ : Satisfies M w Γ) :
    Satisfies M w' Γ :=
  fun B hB => KripkeModel.Forces.mono h (hΓ B hB)

theorem Satisfies.cons {M : KripkeModel α} {w : M.World}
    {Γ : List (Formula α)} {A : Formula α}
    (hA : M.Forces w A) (hΓ : Satisfies M w Γ) : Satisfies M w (A :: Γ) := by
  intro B hB
  cases List.mem_cons.mp hB with
  | inl h => exact h ▸ hA
  | inr h => exact hΓ B h

/-! ## Natural deduction -/

open Formula in
inductive Derives (cl : Bool) : List (Formula α) → Formula α → Prop
  | hyp   {Γ A}     : A ∈ Γ → Derives cl Γ A
  | topI  {Γ}       : Derives cl Γ top
  | botE  {Γ A}     : Derives cl Γ bot → Derives cl Γ A
  | notI  {Γ A}     : Derives cl (A :: Γ) bot → Derives cl Γ (not A)
  | notE  {Γ A}     : Derives cl Γ (not A) → Derives cl Γ A → Derives cl Γ bot
  | andI  {Γ A B}   : Derives cl Γ A → Derives cl Γ B → Derives cl Γ (and A B)
  | andE₁ {Γ A B}   : Derives cl Γ (and A B) → Derives cl Γ A
  | andE₂ {Γ A B}   : Derives cl Γ (and A B) → Derives cl Γ B
  | orI₁  {Γ A B}   : Derives cl Γ A → Derives cl Γ (or A B)
  | orI₂  {Γ A B}   : Derives cl Γ B → Derives cl Γ (or A B)
  | orE   {Γ A B C} : Derives cl Γ (or A B) → Derives cl (A :: Γ) C →
                      Derives cl (B :: Γ) C → Derives cl Γ C
  | impI  {Γ A B}   : Derives cl (A :: Γ) B → Derives cl Γ (imp A B)
  | impE  {Γ A B}   : Derives cl Γ (imp A B) → Derives cl Γ A → Derives cl Γ B
  | iffI  {Γ A B}   : Derives cl (A :: Γ) B → Derives cl (B :: Γ) A →
                      Derives cl Γ (iff A B)
  | iffE₁ {Γ A B}   : Derives cl Γ (iff A B) → Derives cl Γ A → Derives cl Γ B
  | iffE₂ {Γ A B}   : Derives cl Γ (iff A B) → Derives cl Γ B → Derives cl Γ A
  /-- Excluded middle: available only when `cl = true`. -/
  | em    {Γ A}     : cl = true → Derives cl Γ (or A (not A))

def kuroda (f: Formula α) : Formula α :=
     match f with
       | Formula.atom _  => Formula.not ∘ Formula.not $ f
       | Formula.top => Formula.top
       | Formula.bot => Formula.bot
       | Formula.not _   => Formula.not ∘ Formula.not $ f
       | Formula.and _ _ => Formula.not ∘ Formula.not $ f
       | Formula.or _ _  => Formula.not ∘ Formula.not $ f
       | Formula.imp _ _ => Formula.not ∘ Formula.not $ f
       | Formula.iff _ _ => Formula.not ∘ Formula.not $ f

scoped notation:25 Γ:26 " ⊢[" cl "] " A:26 => Derives cl Γ A
scoped notation:25 Γ:26 " ⊢ " A:26 => Derives false Γ A
scoped notation:25 Γ:26 " ⊢ₐ " A:26 => Derives true Γ A

def Provable (A : Formula α) : Prop := [] ⊢ A

/-! ## Metatheorems -/

theorem soundness {Γ : List (Formula α)} {A : Formula α} :
    Γ ⊢ A → Γ ⊨ A := by
  intro h
  induction h with
  | hyp hA => exact fun _ _ hv => hv _ hA
  | topI => exact fun _ _ _ => trivial
  | botE _ ih => exact fun M w hv => (ih M w hv).elim
  | notI _ ih => exact fun M w hv w' h hA => ih M w' (.cons hA (hv.mono h))
  | notE _ _ ih₁ ih₂ => exact fun M w hv => ih₁ M w hv w (M.refl w) (ih₂ M w hv)
  | andI _ _ ih₁ ih₂ => exact fun M w hv => ⟨ih₁ M w hv, ih₂ M w hv⟩
  | andE₁ _ ih => exact fun M w hv => (ih M w hv).1
  | andE₂ _ ih => exact fun M w hv => (ih M w hv).2
  | orI₁ _ ih => exact fun M w hv => .inl (ih M w hv)
  | orI₂ _ ih => exact fun M w hv => .inr (ih M w hv)
  | orE _ _ _ ih ih₁ ih₂ =>
    exact fun M w hv => (ih M w hv).elim (fun h => ih₁ M w (.cons h hv))
                                         (fun h => ih₂ M w (.cons h hv))
  | impI _ ih => exact fun M w hv w' h hA => ih M w' (.cons hA (hv.mono h))
  | impE _ _ ih₁ ih₂ => exact fun M w hv => ih₁ M w hv w (M.refl w) (ih₂ M w hv)
  | iffI _ _ ih₁ ih₂ =>
    exact fun M w hv w' h => ⟨fun hA => ih₁ M w' (.cons hA (hv.mono h)),
                              fun hB => ih₂ M w' (.cons hB (hv.mono h))⟩
  | iffE₁ _ _ ih₁ ih₂ =>
    exact fun M w hv => (ih₁ M w hv w (M.refl w)).mp (ih₂ M w hv)
  | iffE₂ _ _ ih₁ ih₂ =>
    exact fun M w hv => (ih₁ M w hv w (M.refl w)).mpr (ih₂ M w hv)
  | em h => nomatch h

theorem completeness {Γ : List (Formula α)} {A : Formula α} :
    Γ ⊨ A → Γ ⊢ A := by
  sorry

theorem valid_iff_provable {A : Formula α} : Valid A ↔ Provable A :=
  ⟨completeness, soundness⟩

open Formula in
/-- Excluded middle is not derivable: the two-world model `false ≤ true`,
with the atom true only at `true`, refutes it at `false`. -/
theorem not_em (a : α) : ¬ Provable (or (atom a) (not (atom a))) := by
  intro h
  let M : KripkeModel α :=
    { World := Bool
      le    := fun u v => u = true → v = true
      refl  := fun _ h => h
      trans := fun h₁ h₂ h => h₂ (h₁ h)
      val   := fun w _ => w = true
      mono  := fun h hw => h hw }
  have := soundness h M false (fun _ hB => nomatch hB)
  simp only [KripkeModel.Forces] at this
  rcases this with h₁ | h₂
  · exact Bool.false_ne_true h₁
  · exact h₂ true (fun h => nomatch h) rfl


/-- A derivation stays valid in a larger context. -/
theorem Derives.mono {cl : Bool} {Γ Δ : List (Formula α)} {A : Formula α}
    (h : Γ ⊢[cl] A) (hs : Γ ⊆ Δ) : Δ ⊢[cl] A := by
  induction h generalizing Δ with
  | hyp hA => exact .hyp (hs hA)
  | topI => exact .topI
  | botE _ ih => exact .botE (ih hs)
  | notI _ ih => exact .notI (ih (List.cons_subset_cons _ hs))
  | notE _ _ ih₁ ih₂ => exact .notE (ih₁ hs) (ih₂ hs)
  | andI _ _ ih₁ ih₂ => exact .andI (ih₁ hs) (ih₂ hs)
  | andE₁ _ ih => exact .andE₁ (ih hs)
  | andE₂ _ ih => exact .andE₂ (ih hs)
  | orI₁ _ ih => exact .orI₁ (ih hs)
  | orI₂ _ ih => exact .orI₂ (ih hs)
  | orE _ _ _ ih ih₁ ih₂ =>
    exact .orE (ih hs) (ih₁ (List.cons_subset_cons _ hs))
                       (ih₂ (List.cons_subset_cons _ hs))
  | impI _ ih => exact .impI (ih (List.cons_subset_cons _ hs))
  | impE _ _ ih₁ ih₂ => exact .impE (ih₁ hs) (ih₂ hs)
  | iffI _ _ ih₁ ih₂ =>
    exact .iffI (ih₁ (List.cons_subset_cons _ hs))
                (ih₂ (List.cons_subset_cons _ hs))
  | iffE₁ _ _ ih₁ ih₂ => exact .iffE₁ (ih₁ hs) (ih₂ hs)
  | iffE₂ _ _ ih₁ ih₂ => exact .iffE₂ (ih₁ hs) (ih₂ hs)
  | em h => exact .em h

theorem weakening {cl : Bool} {A' B' : Formula α} {Γ : List (Formula α)} :
  Γ ⊢[cl] A' → B' :: Γ ⊢[cl] A' := by
  intro w
  induction w with
    |@hyp ls p h =>
      apply Derives.hyp
      simp
      have dec : p = B' ∨ ¬ p = B' :=
      by grind
      cases dec
      left
      assumption
      right
      assumption
    |@topI ls =>
      apply Derives.topI
    |@botE ls p h h' =>
      apply Derives.botE
      assumption
    |@notE ls p h h' v v'=>
      apply Derives.notE v
      assumption
    |@andE₁ ls p h h' v =>
      apply Derives.andE₁ v
    |@andI ls p h h' v v' w' =>
      apply Derives.andI
      assumption
      assumption
    |@andE₂ ls p h h' v =>
      apply Derives.andE₂ v
    |@notI ls p h v =>
      apply Derives.notI
      exact Derives.mono v (List.Perm.swap p B' ls).subset
    |@orI₁ ls p h h' v =>
      apply Derives.orI₁ v
    |@orI₂ ls p h h' v =>
      apply Derives.orI₂ v
    |@orE ls p h c h₁ h₂ h₃ v v₁ v₂ =>
      apply Derives.orE v
      exact Derives.mono v₁ (List.Perm.swap p B' ls).subset
      exact Derives.mono v₂ (List.Perm.swap h B' ls).subset
    |@impI ls p h h' v =>
      apply Derives.impI
      exact Derives.mono v (List.Perm.swap p B' ls).subset
    |@impE ls p h h' h'' v v' =>
      apply Derives.impE v v'
    |@iffI ls p h h' h'' v v' =>
      apply Derives.iffI
      exact Derives.mono v (List.Perm.swap p B' ls).subset
      exact Derives.mono v' (List.Perm.swap h B' ls).subset
    |@iffE₁ ls p h h' h'' v v' =>
      apply Derives.iffE₁ v v'
    |@iffE₂ ls p h h' h'' v v' =>
      apply Derives.iffE₂ v v'
    |@em ls p h =>
      exact Derives.em h


theorem not_not {cl : Bool} {A' : Formula α} {Γ : List (Formula α)} :
  Γ ⊢[cl] A' → Γ ⊢[cl] (Formula.not ∘ Formula.not $ A') := by
  intro w
  induction w with
    |@hyp ls p h =>
      apply Derives.notI
      have h': ls ⊢[cl] p := by
        constructor
        assumption
      apply @Derives.notE _ _ _ p
      apply Derives.hyp
      simp
      apply weakening
      assumption
    |@topI ls =>
      apply Derives.notI
      apply Derives.botE
      have ex: Formula.top.not :: ls ⊢[cl] Formula.top := by
        apply @Derives.topI _ _ (Formula.top.not :: ls)
      apply @Derives.notE _ _ _ (Formula.top)
      apply Derives.hyp
      simp
      apply Derives.topI
    |@botE ls v v' p =>
      apply Derives.botE
      assumption
    |@notI ls p h _ =>
      apply Derives.notI
      exact Derives.notE (Derives.hyp (by simp)) (weakening (Derives.notI h))
    |@notE ls p h h' _ _ =>
      apply Derives.notI
      exact Derives.notE (Derives.hyp (by simp)) (weakening (Derives.notE h h'))
    |@andI ls p q h h' _ _ =>
      apply Derives.notI
      exact Derives.notE (Derives.hyp (by simp)) (weakening (Derives.andI h h'))
    |@andE₁ ls p q h _ =>
      apply Derives.notI
      exact Derives.notE (Derives.hyp (by simp)) (weakening (Derives.andE₁ h))
    |@andE₂ ls p q h _ =>
      apply Derives.notI
      exact Derives.notE (Derives.hyp (by simp)) (weakening (Derives.andE₂ h))
    |@orI₁ ls p q h _ =>
      apply Derives.notI
      exact Derives.notE (Derives.hyp (by simp)) (weakening (Derives.orI₁ (B := q) h))
    |@orI₂ ls p q h _ =>
      apply Derives.notI
      exact Derives.notE (Derives.hyp (by simp)) (weakening (Derives.orI₂ (A := p) h))
    |@orE ls p q r h h₁ h₂ _ _ _ =>
      apply Derives.notI
      exact Derives.notE (Derives.hyp (by simp)) (weakening (Derives.orE h h₁ h₂))
    |@impI ls p q h _ =>
      apply Derives.notI
      exact Derives.notE (Derives.hyp (by simp)) (weakening (Derives.impI h))
    |@impE ls p q h h' _ _ =>
      apply Derives.notI
      exact Derives.notE (Derives.hyp (by simp)) (weakening (Derives.impE h h'))
    |@iffI ls p q h h' _ _ =>
      apply Derives.notI
      exact Derives.notE (Derives.hyp (by simp)) (weakening (Derives.iffI h h'))
    |@iffE₁ ls p q h h' _ _ =>
      apply Derives.notI
      exact Derives.notE (Derives.hyp (by simp)) (weakening (Derives.iffE₁ h h'))
    |@iffE₂ ls p q h h' _ _ =>
      apply Derives.notI
      exact Derives.notE (Derives.hyp (by simp)) (weakening (Derives.iffE₂ h h'))
    |@em ls p h =>
      apply Derives.notI
      exact Derives.notE (Derives.hyp (by simp)) (weakening (Derives.em (A := p) h))

theorem test: ¬ ¬ (p ∨ ¬ p) := by
  intro h
  apply h
  right
  intro p'
  have x: (p ∨ ¬ p) := by
    constructor
    assumption
  grind


/-- Glivenko's theorem: `kuroda` puts `¬¬` in front of every formula except
`⊤` and `⊥` (for `⊥`, `¬¬⊥ ⊢ ⊥` intuitionistically). -/
theorem conv {A' : Formula α} {Γ : List (Formula α)} : Γ ⊢ₐ A' → Γ ⊢ kuroda A' := by
  intros a
  induction a with
    |@hyp w h a =>
      cases h with
        |atom a' =>
          simp [kuroda]
          apply not_not
          apply Derives.hyp
          assumption
        |top =>
          simp [kuroda]
          apply Derives.hyp
          assumption
        |bot =>
          simp [kuroda]
          apply Derives.hyp
          assumption
        | @not | @and | @or | @imp | @iff =>
          simp [kuroda]
          apply not_not
          apply Derives.hyp
          assumption
      |@topI e =>
        simp [kuroda]
        apply Derives.topI
      |@botE e r e e' =>
        simp [kuroda]
        cases r with
          |atom a' =>
            simp [kuroda] at *
            apply Derives.notI
            apply weakening
            assumption
          |top =>
            simp
            apply Derives.topI
          |bot =>
            simp [kuroda] at *
            assumption
          |@not | @and |@or |@imp |@iff =>
            simp [kuroda] at *
            apply Derives.notI
            apply weakening
            assumption
      |@em k e a =>
        simp [kuroda]
        apply Derives.notI
        apply @Derives.notE _ _ _ (Formula.not (Formula.or e (Formula.not e)))
        apply not_not
        apply Derives.orI₂
        apply Derives.notI
        have x : e :: (Formula.not (Formula.or e (Formula.not e))) :: k ⊢ (Formula.or e (Formula.not e)) := by
          apply @Derives.orI₁
          apply Derives.hyp
          simp
        have k' : e.or e.not :: (e.or e.not).not :: k ⊢ Formula.bot := by
          apply @Derives.notE _ _ _ (e.or e.not)
          apply @Derives.hyp
          simp
          apply @Derives.hyp
          simp
        clear x a
        apply Derives.notE (weakening (Derives.notI k'))
        apply Derives.orI₁
        apply Derives.hyp
        simp
        apply Derives.hyp
        simp

end IPL

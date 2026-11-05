module

public import sunlet.class_selection
public import sunlet.orbit_height
public import sunlet.exponent_rank

/-! Literal exponent relations and their two height-space factors. -/

@[expose] public section
noncomputable section

namespace Sunlet.ClassKernel

open ClassSelection OrbitHeight

variable {G C : Type*} [AddCommGroup G] [Fintype G] [Fintype C] [LinearOrder C]
  (P : InverseStablePartition G C) (σ : Set C) [DecidablePred (· ∈ σ)]

def Equation (w : ParamVar C C → ℚ) (b c : G) : Prop :=
  w (.s (P.classOf b)) + w (.t (P.classOf c)) +
    (if selectsU P.classOf σ b c then
      w (.u (P.classOf (c - b))) + w (.h (P.classOf c))
    else w (.v (P.classOf (c - b))) + w (.h (P.classOf b))) = 0

def IsRelation (w : ParamVar C C → ℚ) : Prop := ∀ b c, Equation P σ w b c

def kHeight (w : ParamVar C C → ℚ) (i : C) : ℚ :=
  w (.s i) - w (.s P.zeroClass)

def lHeight (w : ParamVar C C → ℚ) (i : C) : ℚ :=
  w (.s i) + w (.h i) - (w (.s P.zeroClass) + w (.h P.zeroClass))

variable (hmin : ∀ i, P.zeroClass ≤ i) (hσ0 : P.zeroClass ∉ σ)
  (w : ParamVar C C → ℚ) (hw : IsRelation P σ w)

include hσ0 hw in
theorem t_value (i : C) :
    w (.t i) = -w (.s i) - w (.h i) - w (.v P.zeroClass) := by
  obtain ⟨b, rfl⟩ := P.surjective i
  have hr := hw b b
  simp [Equation, selectsU, P.zero_class, hσ0] at hr
  linarith

include hσ0 hw in
theorem increasing_row (b c : G) (hbc : P.classOf b < P.classOf c) :
    w (.u (P.classOf (c - b))) =
      w (.v P.zeroClass) + kHeight P w (P.classOf c) - kHeight P w (P.classOf b) := by
  have hr := hw b c
  have hsel : selectsU P.classOf σ b c := Or.inl hbc
  simp only [Equation, if_pos hsel] at hr
  have ht := t_value P σ hσ0 w hw (P.classOf c)
  dsimp [kHeight]
  linarith

include hσ0 hw in
theorem decreasing_row (b c : G) (hcb : P.classOf c < P.classOf b) :
    w (.v (P.classOf (c - b))) =
      w (.v P.zeroClass) + lHeight P w (P.classOf c) - lHeight P w (P.classOf b) := by
  have hr := hw b c
  have hsel : ¬ selectsU P.classOf σ b c := by
    simp only [selectsU]
    exact not_or.mpr ⟨not_lt.mpr hcb.le, fun h => hcb.ne h.1.symm⟩
  simp only [Equation, if_neg hsel] at hr
  have ht := t_value P σ hσ0 w hw (P.classOf c)
  dsimp [lHeight]
  linarith

include hmin hσ0 hw in
theorem u_value (i : C) (hi : i ≠ P.zeroClass) :
    w (.u i) = w (.v P.zeroClass) + kHeight P w i := by
  obtain ⟨c, hc⟩ := P.surjective i
  have hlt : P.classOf 0 < P.classOf c := by
    rw [P.zero_class, hc]
    exact lt_of_le_of_ne (hmin i) (Ne.symm hi)
  have hr := increasing_row P σ hσ0 w hw 0 c hlt
  simpa only [sub_zero, hc, P.zero_class, kHeight, sub_self, sub_zero] using hr

include hmin hσ0 hw in
theorem v_value (i : C) (hi : i ≠ P.zeroClass) :
    w (.v i) = w (.v P.zeroClass) - lHeight P w i := by
  obtain ⟨c, hc⟩ := P.surjective i
  have hlt : P.classOf 0 < P.classOf c := by
    rw [P.zero_class, hc]
    exact lt_of_le_of_ne (hmin i) (Ne.symm hi)
  have hr := decreasing_row P σ hσ0 w hw c 0 hlt
  simpa only [zero_sub, P.neg_class, hc, P.zero_class, lHeight, sub_self, add_zero] using hr

theorem difference_class_ne_zero (b c : G) (hbc : P.classOf b < P.classOf c) :
    P.classOf (c - b) ≠ P.zeroClass := by
  intro he
  have hcb := sub_eq_zero.mp ((P.zero_iff _).mp he)
  exact hbc.ne (congrArg P.classOf hcb.symm)

include hmin hσ0 hw in
theorem kHeight_mem : kHeight P w ∈ P.heightSpace := by
  constructor
  · simp [kHeight]
  · intro b c hbc
    have hr := increasing_row P σ hσ0 w hw b c hbc
    have hu := u_value P σ hmin hσ0 w hw _ (difference_class_ne_zero P b c hbc)
    linarith

include hmin hσ0 hw in
theorem lHeight_mem : lHeight P w ∈ P.heightSpace := by
  constructor
  · simp [lHeight]
  · intro b c hbc
    have hr := decreasing_row P σ hσ0 w hw c b hbc
    have hv := v_value P σ hmin hσ0 w hw _ (difference_class_ne_zero P b c hbc)
    have hd : P.classOf (b - c) = P.classOf (c - b) := by
      rw [← neg_sub c b, P.neg_class]
    rw [hd] at hr
    linarith

include hmin hσ0 hw in
theorem kHeight_vanishes (i : C) (hi : P.sameClassDifference i) (hσ : i ∈ σ) :
    kHeight P w i = 0 := by
  obtain ⟨hi0, b, c, hbc, _, hd⟩ := hi
  have hr := hw b c
  have hsel : selectsU P.classOf σ b c := Or.inr ⟨hbc, hd ▸ hσ⟩
  simp only [Equation, if_pos hsel, hd, hbc] at hr
  have ht := t_value P σ hσ0 w hw (P.classOf c)
  have hu := u_value P σ hmin hσ0 w hw i hi0
  linarith

include hmin hσ0 hw in
theorem lHeight_vanishes (i : C) (hi : P.sameClassDifference i) (hσ : i ∉ σ) :
    lHeight P w i = 0 := by
  obtain ⟨hi0, b, c, hbc, _, hd⟩ := hi
  have hr := hw b c
  have hsel : ¬ selectsU P.classOf σ b c := by simp [selectsU, hbc, hd, hσ]
  simp only [Equation, if_neg hsel, hd, hbc] at hr
  have ht := t_value P σ hσ0 w hw (P.classOf c)
  have hv := v_value P σ hmin hσ0 w hw i hi0
  linarith

/-- The condition on the two copies of the height space that the choice of
opposite same-class signs must establish. This is an intermediate property,
not an assumed replacement for a principal theorem. -/
def KillsHeights : Prop :=
  (∀ x ∈ P.heightSpace,
    (∀ i, P.sameClassDifference i → i ∈ σ → x i = 0) → x = 0) ∧
  (∀ x ∈ P.heightSpace,
    (∀ i, P.sameClassDifference i → i ∉ σ → x i = 0) → x = 0)

include hmin hσ0 hw in
theorem relation_canonical (hkill : KillsHeights P σ) :
    w = SelectedRelations.canonical P.zeroClass
      (w (.s P.zeroClass)) (w (.s P.zeroClass) + w (.h P.zeroClass))
      (w (.v P.zeroClass)) (w (.u P.zeroClass)) := by
  have hk := hkill.1 (kHeight P w) (kHeight_mem P σ hmin hσ0 w hw)
    (kHeight_vanishes P σ hmin hσ0 w hw)
  have hl := hkill.2 (lHeight P w) (lHeight_mem P σ hmin hσ0 w hw)
    (lHeight_vanishes P σ hmin hσ0 w hw)
  have hs (i : C) : w (.s i) = w (.s P.zeroClass) := by
    have he := congrFun hk i
    dsimp [kHeight] at he
    linarith
  have hh (i : C) : w (.h i) = w (.h P.zeroClass) := by
    have he := congrFun hl i
    dsimp [lHeight] at he
    linarith [hs i]
  funext i
  cases i with
  | s j => exact hs j
  | h j => simp only [SelectedRelations.canonical]; linarith [hh j]
  | t j =>
      simp only [SelectedRelations.canonical]
      linarith [t_value P σ hσ0 w hw j, hs j, hh j]
  | u j =>
      by_cases hj : j = P.zeroClass
      · simp [SelectedRelations.canonical, hj]
      · simp only [SelectedRelations.canonical, if_neg hj]
        have hu := u_value P σ hmin hσ0 w hw j hj
        rw [hk] at hu
        simpa using hu
  | v j =>
      simp only [SelectedRelations.canonical]
      by_cases hj : j = P.zeroClass
      · rw [hj]
      · have hv := v_value P σ hmin hσ0 w hw j hj
        rw [hl] at hv
        simpa using hv

include hσ0 in
theorem canonical_isRelation (s k v u : ℚ) :
    IsRelation P σ (SelectedRelations.canonical P.zeroClass s k v u) := by
  intro b c
  unfold Equation
  by_cases hsel : selectsU P.classOf σ b c
  · have ha : P.classOf (c - b) ≠ P.zeroClass := by
      intro he
      have hcb := sub_eq_zero.mp ((P.zero_iff _).mp he)
      subst c
      simpa [selectsU, P.zero_class, hσ0] using hsel
    simp only [if_pos hsel, SelectedRelations.canonical, if_neg ha]
    ring
  · simp only [if_neg hsel, SelectedRelations.canonical]
    ring

end Sunlet.ClassKernel

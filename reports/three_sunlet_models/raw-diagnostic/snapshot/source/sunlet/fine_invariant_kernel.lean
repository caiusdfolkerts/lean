module

public import sunlet.fine_odd_kernel

/-! Descent of invariant fine relations to the actual coarse height kernel. -/

@[expose] public section
noncomputable section

namespace Sunlet.FineOddKernel

variable {G C D : Type*} [AddCommGroup G] [Fintype G] [Fintype C]
  [DecidableEq C] [Fintype D] [LinearOrder D]

def representative (P : OrbitHeight.InverseStablePartition G D) (i : D) : G :=
  Classical.choose (P.surjective i)

theorem class_representative (P : OrbitHeight.InverseStablePartition G D) (i : D) :
    P.classOf (representative P i) = i := Classical.choose_spec (P.surjective i)

def descend (P : OrbitHeight.InverseStablePartition G D) (q : G → C)
    (w : ParamVar C C → ℚ) : ParamVar D D → ℚ :=
  fun j => w (mapParam (q ∘ representative P) j)

theorem descend_value (P : OrbitHeight.InverseStablePartition G D) (q : G → C)
    (e : C ≃ C) (he : ∀ a, e (q a) = q (-a))
    (hfib : ∀ a b, P.classOf a = P.classOf b → q a = q b ∨ q (-a) = q b)
    (w : ParamVar C C → ℚ) (hinv : negColumns e w = w) (j : ParamVar G G) :
    descend P q w (mapParam P.classOf j) = w (mapParam q j) := by
  have hv (a : G) (T : C → ParamVar C C)
      (hT : ∀ i, mapParam e (T i) = T (e i)) :
      w (T (q (representative P (P.classOf a)))) = w (T (q a)) := by
    rcases hfib (representative P (P.classOf a)) a (class_representative P _) with h | h
    · rw [h]
    · have hn := congrFun hinv (T (q (representative P (P.classOf a))))
      change w (mapParam e (T (q (representative P (P.classOf a))))) = _ at hn
      rw [hT,he,h] at hn
      exact hn.symm
  cases j with
  | s a => exact hv a ParamVar.s (fun _ => rfl)
  | t a => exact hv a ParamVar.t (fun _ => rfl)
  | h a => exact hv a ParamVar.h (fun _ => rfl)
  | u a => exact hv a ParamVar.u (fun _ => rfl)
  | v a => exact hv a ParamVar.v (fun _ => rfl)

theorem descend_relation (P : OrbitHeight.InverseStablePartition G D) (q : G → C)
    (e : C ≃ C) (he : ∀ a, e (q a) = q (-a))
    (hfib : ∀ a b, P.classOf a = P.classOf b → q a = q b ∨ q (-a) = q b)
    (σ : Set D) [DecidablePred (· ∈ σ)]
    (w : ParamVar C C → ℚ) (hinv : negColumns e w = w)
    (hw : IsRelation q P.classOf σ w) :
    ClassKernel.IsRelation P σ (descend P q w) := by
  intro b c
  have hs := descend_value P q e he hfib w hinv (.s b)
  have ht := descend_value P q e he hfib w hinv (.t c)
  have hu := descend_value P q e he hfib w hinv (.u (c-b))
  have hv := descend_value P q e he hfib w hinv (.v (c-b))
  have hh := descend_value P q e he hfib w hinv (.h c)
  have hh' := descend_value P q e he hfib w hinv (.h b)
  simp only [mapParam] at hs ht hu hv hh hh'
  unfold ClassKernel.Equation
  rw [hs,ht,hu,hv,hh,hh']
  exact hw b c

theorem invariant_canonical (P : OrbitHeight.InverseStablePartition G D)
    (q : G → C) (hq : Function.Surjective q) (z : C)
    (hq0 : ∀ a, q a = z ↔ a = 0)
    (e : C ≃ C) (he : ∀ a, e (q a) = q (-a))
    (hfib : ∀ a b, P.classOf a = P.classOf b → q a = q b ∨ q (-a) = q b)
    (σ : Set D) [DecidablePred (· ∈ σ)]
    (hmin : ∀ i, P.zeroClass ≤ i) (hσ : P.zeroClass ∉ σ)
    (hkill : ClassKernel.KillsHeights P σ)
    (w : ParamVar C C → ℚ) (hinv : negColumns e w = w)
    (hw : IsRelation q P.classOf σ w) :
    w = SelectedRelations.canonical z (w (.s z)) (w (.s z)+w (.h z))
      (w (.v z)) (w (.u z)) := by
  have hzero : q 0 = z := (hq0 0).mpr rfl
  have hc := ClassKernel.relation_canonical P σ hmin hσ (descend P q w)
    (descend_relation P q e he hfib σ w hinv hw) hkill
  have hs0 : descend P q w (.s P.zeroClass) = w (.s z) := by
    simpa only [mapParam,P.zero_class,hzero] using descend_value P q e he hfib w hinv (.s 0)
  have hh0 : descend P q w (.h P.zeroClass) = w (.h z) := by
    simpa only [mapParam,P.zero_class,hzero] using descend_value P q e he hfib w hinv (.h 0)
  have hv0 : descend P q w (.v P.zeroClass) = w (.v z) := by
    simpa only [mapParam,P.zero_class,hzero] using descend_value P q e he hfib w hinv (.v 0)
  have hu0 : descend P q w (.u P.zeroClass) = w (.u z) := by
    simpa only [mapParam,P.zero_class,hzero] using descend_value P q e he hfib w hinv (.u 0)
  rw [hs0,hh0,hv0,hu0] at hc
  have hv (j : ParamVar G G) :
      w (mapParam q j) = SelectedRelations.canonical z
        (w (.s z)) (w (.s z)+w (.h z)) (w (.v z)) (w (.u z)) (mapParam q j) := by
    have h := congrFun hc (mapParam P.classOf j)
    rw [descend_value P q e he hfib w hinv] at h
    cases j with
    | s a => exact h
    | t a => exact h
    | h a => exact h
    | v a => exact h
    | u a =>
        by_cases ha : a = 0
        · have hp : P.classOf a = P.zeroClass := (P.zero_iff a).mpr ha
          have hq' : q a = z := (hq0 a).mpr ha
          simpa only [mapParam, SelectedRelations.canonical, if_pos hp, if_pos hq'] using h
        · have hp : P.classOf a ≠ P.zeroClass := fun h => ha ((P.zero_iff a).mp h)
          have hq' : q a ≠ z := fun h => ha ((hq0 a).mp h)
          simpa only [mapParam, SelectedRelations.canonical, if_neg hp, if_neg hq'] using h
  funext j
  cases j with
  | s i => obtain ⟨a,rfl⟩ := hq i; exact hv (.s a)
  | t i => obtain ⟨a,rfl⟩ := hq i; exact hv (.t a)
  | h i => obtain ⟨a,rfl⟩ := hq i; exact hv (.h a)
  | u i => obtain ⟨a,rfl⟩ := hq i; exact hv (.u a)
  | v i => obtain ⟨a,rfl⟩ := hq i; exact hv (.v a)

/-- A good coarse initial system always yields the full fine dimension.
The possible odd kernel is discharged by the proved generating-support route. -/
theorem dimension_of_coarse_good_order {K : Type*} [Field K] [Infinite K]
    (P : OrbitHeight.InverseStablePartition G D)
    (q : G → C) (hq : Function.Surjective q) (z : C)
    (hq0 : ∀ a, q a = z ↔ a = 0)
    (p : C → D) (hp : ∀ a, p (q a) = P.classOf a)
    (e : C ≃ C) (he : ∀ a, e (q a) = q (-a))
    (hfib : ∀ a b, P.classOf a = P.classOf b → q a = q b ∨ q (-a) = q b)
    (hmin : ∀ i, P.zeroClass ≤ i) (hgood : P.GoodHeightOrder)
    (hm : 5 ≤ Fintype.card G) :
    ringKrullDim (MvPolynomial (G × G) K ⧸ MvPolynomial.vanishingIdeal K
      (PolynomialImage.closure (Identified.coordinatePolynomial (K := K) q))) =
        (5 * Fintype.card C - 4 : ℕ) := by
  classical
  obtain ⟨σ,hσ,hkill⟩ := P.exists_signs_killing_heights hgood
  have hzero : q 0 = z := (hq0 0).mpr rfl
  have hpz : p z = P.zeroClass := by simpa only [hzero,P.zero_class] using hp 0
  by_cases hinv : ∀ w, IsRelation q P.classOf σ w → negColumns e w = w
  · apply CoarseSelection.imageClosure_dimension_eq q p σ hq z hq0 (hpz ▸ hσ)
    intro w hw
    have hw' : IsRelation q P.classOf σ w := by
      intro b c
      simpa only [CoarseSelection.Equation,CoarseSelection.selectsU,
        ClassSelection.selectsU,Function.comp_apply,hp,Equation] using hw b c
    exact invariant_canonical P q hq z hq0 e he hfib σ hmin hσ hkill w (hinv w hw') hw'
  · push_neg at hinv
    obtain ⟨w,hw,hne⟩ := hinv
    have hn := relation_neg q P.classOf σ e he P.neg_class w hw
    have hd := relation_sub q P.classOf σ w (negColumns e w) hw hn
    have ho := difference_odd q e he w
    have hdne : w-negColumns e w ≠ 0 := by
      intro h
      exact hne (sub_eq_zero.mp h).symm
    exact dimension_of_nonzero_odd q hq z hq0 P.classOf σ
      (by simpa only [P.zero_class] using hσ)
      (by intro a; simpa only [P.zero_class] using hmin (P.classOf a))
      (by intro a; simpa only [P.zero_class] using P.zero_iff a)
      P.neg_class hfib (w-negColumns e w) hd ho hdne hm

end Sunlet.FineOddKernel

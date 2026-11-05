import bier.cone_coordinates

/-! The canonical Bier cone contains a genuine neighborhood of its apex. -/

noncomputable section

namespace Bier

open Set Topology

variable {V : Type*} [Fintype V] [DecidableEq V]

def thresholdCoordinates (x : V → ℝ) (t : ℝ) : Option (V ⊕ V) → ℝ
  | none => 1 - ∑ v, |x v - t|
  | some (.inl v) => max (x v - t) 0
  | some (.inr v) => max (t - x v) 0

theorem thresholdCoordinates_admissible (face : Finset V → Prop) (x : V → ℝ) (t : ℝ)
    (hface : face (Finset.univ.filter (fun v => t < x v)))
    (hnonface : ¬ face (Finset.univ.filter (fun v => t ≤ x v)))
    (hsize : ∑ v, |x v - t| ≤ 1) :
    ConeCoordinates face (thresholdCoordinates x t) := by
  constructor
  · intro a
    cases a with
    | none => exact sub_nonneg.mpr hsize
    | some a => cases a <;> exact le_max_right _ _
  · simp only [Fintype.sum_option, Fintype.sum_sum_type, thresholdCoordinates]
    have hsum : ∑ v, max (x v - t) 0 + ∑ v, max (t - x v) 0 = ∑ v, |x v - t| := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro v _
      rcases le_total t (x v) with h | h
      · rw [max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h),
          abs_of_nonneg (sub_nonneg.mpr h), add_zero]
      · rw [max_eq_right (sub_nonpos.mpr h), max_eq_left (sub_nonneg.mpr h),
          abs_of_nonpos (sub_nonpos.mpr h), zero_add]
        ring
    linarith
  · convert hface using 1
    congr 1
    ext v
    simp [thresholdCoordinates, lt_max_iff, sub_pos]
  · have heq : Finset.univ.filter (fun v => thresholdCoordinates x t (some (.inr v)) = 0) =
        Finset.univ.filter (fun v => t ≤ x v) := by
      ext v
      simp [thresholdCoordinates, max_eq_right_iff, sub_nonpos]
    rw [heq]
    exact hnonface
  · intro v
    rcases le_total t (x v) with h | h
    · exact Or.inr (max_eq_right (sub_nonpos.mpr h))
    · exact Or.inl (max_eq_right (sub_nonpos.mpr h))

theorem signed_thresholdCoordinates (x : V → ℝ) (t : ℝ) (v : V) :
    signedCoordinate (thresholdCoordinates x t) v = x v - t := by
  change max (x v - t) 0 - max (t - x v) 0 = x v - t
  rw [show t - x v = -(x v - t) by ring]
  exact max_zero_sub_max_neg_zero_eq_self _

def extendCoordinate (v₀ : V) (y : {v : V // v ≠ v₀} → ℝ) (v : V) : ℝ :=
  if h : v = v₀ then 0 else y ⟨v, h⟩

@[simp] theorem extendCoordinate_self (v₀ : V) (y : {v : V // v ≠ v₀} → ℝ) :
    extendCoordinate v₀ y v₀ = 0 := by simp [extendCoordinate]

@[simp] theorem extendCoordinate_subtype (v₀ : V) (y : {v : V // v ≠ v₀} → ℝ)
    (v : {v : V // v ≠ v₀}) : extendCoordinate v₀ y v = y v := by
  simp [extendCoordinate, v.property]

theorem abs_extendCoordinate_le (v₀ : V) (y : {v : V // v ≠ v₀} → ℝ) (v : V) :
    |extendCoordinate v₀ y v| ≤ ‖y‖ := by
  unfold extendCoordinate
  split_ifs with h
  · simpa using norm_nonneg y
  · simpa only [Real.norm_eq_abs] using norm_le_pi_norm y ⟨v, h⟩

theorem coneProjection_thresholdCoordinates (v₀ : V) (y : {v : V // v ≠ v₀} → ℝ) (t : ℝ) :
    coneProjection v₀ (thresholdCoordinates (extendCoordinate v₀ y) t) = y := by
  ext v
  simp [coneProjection_apply, signed_thresholdCoordinates]

theorem coneProjection_image_mem_nhds (face : Finset V → Prop)
    (hempty : face ∅) (hdown : ∀ {s t}, s ⊆ t → face t → face s)
    (hproper : ¬ face Finset.univ) (v₀ : V) :
    coneProjection v₀ '' {w | ConeCoordinates face w} ∈ 𝓝 (0 : {v : V // v ≠ v₀} → ℝ) := by
  classical
  have hc : Continuous (fun y : {v : V // v ≠ v₀} → ℝ =>
      (2 * Fintype.card V : ℝ) * ‖y‖) := continuous_const.mul continuous_norm
  have hn : {y : {v : V // v ≠ v₀} → ℝ | (2 * Fintype.card V : ℝ) * ‖y‖ < 1} ∈ 𝓝 0 :=
    hc.continuousAt.preimage_mem_nhds (Iio_mem_nhds (by simp))
  filter_upwards [hn] with y hy
  obtain ⟨t, ⟨v, hv⟩, hface, hnonface⟩ :=
    exists_face_threshold face hempty hdown hproper (extendCoordinate v₀ y)
  have ht : |t| ≤ ‖y‖ := hv ▸ abs_extendCoordinate_le v₀ y v
  have hsize : ∑ v, |extendCoordinate v₀ y v - t| ≤ 1 := by
    calc
      ∑ v, |extendCoordinate v₀ y v - t| ≤ ∑ _v : V, (‖y‖ + ‖y‖) := by
        exact Finset.sum_le_sum (fun v _ => (abs_sub _ _).trans
          (add_le_add (abs_extendCoordinate_le v₀ y v) ht))
      _ = (2 * Fintype.card V : ℝ) * ‖y‖ := by simp; ring
      _ ≤ 1 := hy.le
  exact ⟨thresholdCoordinates (extendCoordinate v₀ y) t,
    thresholdCoordinates_admissible face _ t hface hnonface hsize,
    coneProjection_thresholdCoordinates v₀ y t⟩

end Bier

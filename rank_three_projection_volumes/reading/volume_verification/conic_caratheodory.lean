module
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Push
public import Lean.Elab.Tactic.SolveByElim
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Finite conic Carathéodory reduction

This proof follows the recovered finite-cone argument, with its finite-minimum
step written explicitly for the pinned library. Only this general algebraic
lemma is needed for the measurable selector; the unrelated face and closedness
results are excluded from its build dependency.
-/
namespace VolumeVerification.ConicCaratheodory
open scoped BigOperators
variable {Index : Type*}

lemma conic_caratheodory {Scalar Ambient : Type*} [Field Scalar] [LinearOrder Scalar] [IsStrictOrderedRing Scalar]
    [AddCommGroup Ambient] [Module Scalar Ambient] [Fintype Index]
    (vectors : Index → Ambient) (coefficients : Index → Scalar) (hc : ∀ index, 0 ≤ coefficients index) :
    ∃ (reducedCoefficients : Index → Scalar) (support : Finset Index), (∀ index, 0 ≤ reducedCoefficients index) ∧ (∀ index ∉ support, reducedCoefficients index = 0) ∧
      LinearIndepOn Scalar vectors support ∧ (∑ index ∈ support, reducedCoefficients index • vectors index) = ∑ index, coefficients index • vectors index := by
  classical
  obtain ⟨support, hs⟩ : ∃ support : Finset Index,
      (∃ reducedCoefficients : Index → Scalar, (∀ index, 0 ≤ reducedCoefficients index) ∧ (∀ index ∉ support, reducedCoefficients index = 0) ∧
        (∑ index ∈ support, reducedCoefficients index • vectors index = ∑ index, coefficients index • vectors index)) ∧
      ∀ smallerSupport : Finset Index, (∃ reducedCoefficients : Index → Scalar, (∀ index, 0 ≤ reducedCoefficients index) ∧ (∀ index ∉ smallerSupport, reducedCoefficients index = 0) ∧
        (∑ index ∈ smallerSupport, reducedCoefficients index • vectors index = ∑ index, coefficients index • vectors index)) → support.card ≤ smallerSupport.card := by
    let S : Set (Finset Index) := {s | ∃ d : Index → Scalar,
      (∀ index, 0 ≤ d index) ∧ (∀ index ∉ s, d index = 0) ∧
        (∑ index ∈ s, d index • vectors index = ∑ index, coefficients index • vectors index)}
    have hS : S.Nonempty := ⟨Finset.univ, coefficients, hc,
      fun index hk => False.elim (hk (Finset.mem_univ index)), by simp⟩
    exact Set.exists_min_image S Finset.card (Set.toFinite S) hS
  by_cases h_lin_dep : ¬ LinearIndepOn Scalar vectors support
  · obtain ⟨reducedCoefficients, hd_nonneg, hd_zero, hd_sum⟩ := hs.left
    obtain ⟨dependency, ha_nonzero, ha_support, ha_sum⟩ : ∃ dependency : Index → Scalar,
        (∃ index ∈ support, dependency index ≠ 0) ∧ (∀ index ∉ support, dependency index = 0) ∧
        (∑ index ∈ support, dependency index • vectors index = 0) ∧ (∃ index ∈ support, dependency index > 0) := by
      obtain ⟨dependency, ha_nonzero, ha_sum⟩ : ∃ dependency : Index → Scalar,
          (∃ index ∈ support, dependency index ≠ 0) ∧ (∀ index ∉ support, dependency index = 0) ∧
          (∑ index ∈ support, dependency index • vectors index = 0) := by
        rw [linearIndepOn_iff'] at h_lin_dep
        push Not at h_lin_dep
        obtain ⟨smallerSupport, weights, ht, hg, chosenIndex, hi, hi'⟩ := h_lin_dep
        refine ⟨fun index => if index ∈ smallerSupport then weights index else 0, ⟨chosenIndex, ht hi, by simpa [hi] using hi'⟩,
          fun index hk => by
            change (if index ∈ smallerSupport then weights index else 0) = 0
            split
            · rename_i hkt
              exact (hk (ht hkt)).elim
            · rfl, ?_⟩
        calc ∑ index ∈ support, (if index ∈ smallerSupport then weights index else 0) • vectors index
            = ∑ index ∈ support, if index ∈ smallerSupport then weights index • vectors index else 0 := by
              refine Finset.sum_congr rfl (fun index _ => ?_); rw [ite_smul, zero_smul]
          _ = ∑ index ∈ support ∩ smallerSupport, weights index • vectors index := Finset.sum_ite_mem support smallerSupport _
          _ = ∑ index ∈ smallerSupport, weights index • vectors index := by rw [Finset.inter_eq_right.mpr ht]
          _ = 0 := hg
      by_cases h_neg : ∀ index ∈ support, dependency index ≤ 0
      · obtain ⟨index, hks, hk⟩ := ha_nonzero
        exact ⟨fun index => -dependency index, ⟨index, hks, neg_ne_zero.mpr hk⟩,
          fun index hk => by simp only [ha_sum.1 index hk, neg_zero],
          by simp [neg_smul, ha_sum.2],
          ⟨index, hks, neg_pos.mpr (lt_of_le_of_ne (h_neg index hks) hk)⟩⟩
      · exact ⟨dependency, ha_nonzero, ha_sum.1, ha_sum.2, by
          push Not at h_neg
          exact h_neg⟩
    obtain ⟨step, hθ_min⟩ : ∃ step,
        (∀ index ∈ support, reducedCoefficients index - step * dependency index ≥ 0) ∧ (∃ index ∈ support, reducedCoefficients index - step * dependency index = 0) := by
      obtain ⟨minimumIndex, hk₀⟩ : ∃ minimumIndex ∈ support, dependency minimumIndex > 0 ∧
          ∀ index ∈ support, dependency index > 0 → reducedCoefficients index / dependency index ≥ reducedCoefficients minimumIndex / dependency minimumIndex := by
        obtain ⟨positiveIndex, hkp⟩ := ha_sum.2
        obtain ⟨minimumIndex, hk₀f, hk₀min⟩ :=
          Finset.exists_min_image (support.filter (fun index => dependency index > 0)) (fun index => reducedCoefficients index / dependency index)
            ⟨positiveIndex, Finset.mem_filter.mpr hkp⟩
        obtain ⟨hk₀s, hk₀pos⟩ := Finset.mem_filter.mp hk₀f
        exact ⟨minimumIndex, hk₀s, hk₀pos, fun index hk hk' =>
          hk₀min index (Finset.mem_filter.mpr ⟨hk, hk'⟩)⟩
      refine ⟨reducedCoefficients minimumIndex / dependency minimumIndex, ?_, minimumIndex, hk₀.1, ?_⟩
      · intro index hk
        by_cases hk' : dependency index > 0
        · have hle : reducedCoefficients minimumIndex / dependency minimumIndex * dependency index ≤ reducedCoefficients index :=
            (le_div_iff₀ hk').1 (hk₀.2.2 index hk hk')
          linarith
        · have h2 : reducedCoefficients minimumIndex / dependency minimumIndex * dependency index ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (div_nonneg (hd_nonneg _) hk₀.2.1.le)
              (le_of_not_gt hk')
          linarith [hd_nonneg index]
      · rw [div_mul_cancel₀ _ hk₀.2.1.ne', sub_self]
    set smallerSupport := support.filter (fun index => reducedCoefficients index - step * dependency index ≠ 0) with ht_def
    have h_t_support : ∀ index, 0 ≤ reducedCoefficients index - step * dependency index := by
      exact fun index => if hk : index ∈ support then hθ_min.1 index hk else by
        simp [hd_zero index hk, ha_support index hk]
    have h_t_zero : ∀ index ∉ smallerSupport, reducedCoefficients index - step * dependency index = 0 := by
      intro index hk
      by_cases hks : index ∈ support
      · by_contra hP
        exact hk (by rw [ht_def]; exact Finset.mem_filter.mpr ⟨hks, hP⟩)
      · rw [hd_zero index hks, ha_support index hks]
        ring
    have h_t_sum : ∑ index ∈ smallerSupport, (reducedCoefficients index - step * dependency index) • vectors index = ∑ index, coefficients index • vectors index := by
      convert congr_arg (fun vector => vector - step • ∑ index ∈ support, dependency index • vectors index) hd_sum using 1
      · rw [Finset.sum_filter_of_ne]
        · simp [sub_smul, Finset.smul_sum, Finset.sum_sub_distrib, smul_smul]
        · exact fun index _ hk' hk'' => hk' <| by rw [hk'', zero_smul]
      · simp [ha_sum.1]
    contrapose! hs
    refine fun _ => ⟨smallerSupport, ⟨fun index => reducedCoefficients index - step * dependency index, h_t_support, h_t_zero, h_t_sum⟩, ?_⟩
    refine Finset.card_lt_card ?_
    rw [ht_def]
    obtain ⟨k₁, hk₁s, hk₁0⟩ := hθ_min.2
    exact ⟨Finset.filter_subset _ _, fun hsub => (Finset.mem_filter.mp (hsub hk₁s)).2 hk₁0⟩
  · exact ⟨hs.1.choose, support, hs.1.choose_spec.1, hs.1.choose_spec.2.1,
      Classical.not_not.mp h_lin_dep, hs.1.choose_spec.2.2⟩

end VolumeVerification.ConicCaratheodory

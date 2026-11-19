module
public import VolumePolynomials.Definitions
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# The complete one-body realization locus

This is the one-body branch of Theorem 1.1, for every positive dimension. It is
proved directly with Lebesgue volume and a dilated unit cube. No mixed-volume
existence theorem is assumed.
-/

noncomputable section

open Set MeasureTheory Finset
open scoped Pointwise BigOperators

namespace VolumePolynomials

def oneIndex (d : ℕ) : MultiIndex 1 d :=
  ⟨fun _ => ⟨d, Nat.lt_succ_self d⟩, by simp⟩

theorem oneIndex_unique {d : ℕ} (α : MultiIndex 1 d) : α = oneIndex d := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simpa [oneIndex] using α.2

instance unique_oneIndex (d : ℕ) : Unique (MultiIndex 1 d) where
  default := oneIndex d
  uniq := oneIndex_unique

@[simp] theorem evaluate_oneVariable {d : ℕ} (c : Coefficients 1 d) (t : Fin 1 → ℝ) :
    evaluate c t = c (oneIndex d) * t 0 ^ d := by
  have hdefault : (default : MultiIndex 1 d) = oneIndex d := oneIndex_unique _
  simp only [evaluate, Fintype.sum_unique, hdefault, oneIndex, Fin.prod_univ_one]

@[simp] theorem sum_coefficients_oneVariable {d : ℕ} (c : Coefficients 1 d) :
    ∑ α, c α = c (oneIndex d) := by
  exact Fintype.sum_unique c

def unitCube (d : ℕ) : Body d where
  carrier := Set.Icc 0 1
  convex' := convex_Icc _ _
  isCompact' := isCompact_Icc
  nonempty' := ⟨0, le_rfl, by intro i; exact zero_le_one⟩

@[simp] theorem bodyVolume_unitCube (d : ℕ) : bodyVolume (unitCube d) = 1 := by
  have h : (0 : Space d) ≤ 1 := fun _ => zero_le_one
  change (volume (Set.Icc (0 : Space d) 1)).toReal = 1
  simpa using Real.volume_Icc_pi_toReal h

theorem exists_body_of_volume {d : ℕ} (hd : 0 < d) {a : ℝ} (ha : 0 ≤ a) :
    ∃ K : Body d, bodyVolume K = a := by
  refine ⟨(a ^ (d : ℝ)⁻¹) • unitCube d, ?_⟩
  rw [bodyVolume_smul _ (Real.rpow_nonneg ha _), bodyVolume_unitCube, mul_one]
  exact Real.rpow_inv_natCast_pow ha hd.ne'

/-- Every nonnegative coefficient, including zero, is realized by one compact
convex body in every positive dimension. -/
theorem oneBody_realizable_iff {d : ℕ} (hd : 0 < d) (c : Coefficients 1 d) :
    c ∈ VolumeLocus 1 d ↔ 0 ≤ c (oneIndex d) := by
  constructor
  · rintro ⟨K, hK⟩
    simpa only [sum_coefficients_oneVariable] using hK.sum_coefficients_nonneg
  · intro hc
    obtain ⟨K, hK⟩ := exists_body_of_volume hd hc
    refine ⟨fun _ => K, fun t ht => ?_⟩
    simp only [volumeFunction, weightedSum, Fin.sum_univ_one, evaluate_oneVariable]
    rw [bodyVolume_smul _ (ht 0), hK, mul_comm]

theorem oneBody_realizable_iff_coefficients_nonneg {d : ℕ} (hd : 0 < d)
    (c : Coefficients 1 d) : c ∈ VolumeLocus 1 d ↔ ∀ α, 0 ≤ c α := by
  rw [oneBody_realizable_iff hd]
  exact ⟨fun h α => oneIndex_unique α ▸ h, fun h => h _⟩

end VolumePolynomials

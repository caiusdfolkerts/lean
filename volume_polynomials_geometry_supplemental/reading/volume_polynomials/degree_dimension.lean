module

public import VolumePolynomials.BodyDimensionGrowth
public import VolumePolynomials.VolumePolynomialExistence
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Degrees and dimensions of every partial Minkowski sum

The support statement is derived from actual volume growth, rather than from
an assumed positivity criterion for mixed volumes. The empty partial sum is
also covered; its value is the point body at zero and its dimension is zero.
-/

open Set Finset MeasureTheory
open scoped BigOperators Pointwise

namespace VolumePolynomials

def partialBodySum {n d : ℕ} (K : Fin n → Body d) (I : Finset (Fin n)) : Body d :=
  ∑ i ∈ I, K i

def partialExponent {n d : ℕ} (I : Finset (Fin n)) (α : MultiIndex n d) : ℕ :=
  ∑ i ∈ I, (α.1 i : ℕ)

def partialWeights {n : ℕ} (I : Finset (Fin n)) (t : ℝ) : Fin n → ℝ :=
  fun i => if i ∈ I then t else 1

theorem partialBodySum_add_compl {n d : ℕ} (K : Fin n → Body d)
    (I : Finset (Fin n)) : partialBodySum K I + partialBodySum K Iᶜ = ∑ i, K i := by
  first
  | classical
    exact Finset.sum_add_sum_compl I K

theorem partialWeights_nonneg {n : ℕ} (I : Finset (Fin n)) {t : ℝ} (ht : 0 ≤ t) :
    ∀ i, 0 ≤ partialWeights I t i := by
  first
  | intro i
    simp only [partialWeights]
    split_ifs <;> positivity

theorem weightedSum_partialWeights {n d : ℕ} (K : Fin n → Body d)
    (I : Finset (Fin n)) (t : ℝ) :
    weightedSum K (partialWeights I t) = t • partialBodySum K I + partialBodySum K Iᶜ := by
  first
  | classical
    rw [weightedSum, partialBodySum, partialBodySum, Finset.smul_sum]
    calc
      (∑ i, partialWeights I t i • K i) =
          ∑ i, if i ∈ I then t • K i else K i := by
        first
        | apply Finset.sum_congr rfl
          intro i _
          by_cases hi : i ∈ I <;> simp [partialWeights, hi]
      _ = (∑ i ∈ I, t • K i) + ∑ i ∈ Iᶜ, K i := by
        first
        | simpa only [Finset.piecewise, Finset.univ_inter, Finset.compl_eq_univ_sdiff] using
            Finset.sum_piecewise (Finset.univ : Finset (Fin n)) I (fun i => t • K i) K

theorem evaluate_partialWeights {n d : ℕ} (c : Coefficients n d)
    (I : Finset (Fin n)) (t : ℝ) :
    evaluate c (partialWeights I t) = ∑ α, c α * t ^ partialExponent I α := by
  first
  | classical
    apply Finset.sum_congr rfl
    intro α _
    congr 1
    calc
      (∏ i, partialWeights I t i ^ (α.1 i : ℕ)) =
          ∏ i, if i ∈ I then t ^ (α.1 i : ℕ) else 1 := by
        first
        | apply Finset.prod_congr rfl
          intro i _
          by_cases hi : i ∈ I <;> simp [partialWeights, hi]
      _ = ∏ i ∈ I, t ^ (α.1 i : ℕ) := by
        first
        | exact Fintype.prod_ite_mem I _
      _ = t ^ partialExponent I α := Finset.prod_pow_eq_pow_sum I _ t

theorem Realizes.partial_volume_formula {n d : ℕ} {K : Fin n → Body d}
    {c : Coefficients n d} (h : Realizes K c) (I : Finset (Fin n))
    {t : ℝ} (ht : 0 ≤ t) :
    bodyVolume (t • partialBodySum K I + partialBodySum K Iᶜ) =
      ∑ α, c α * t ^ partialExponent I α := by
  first
  | have hv := h (partialWeights I t) (partialWeights_nonneg I ht)
    rw [evaluate_partialWeights, volumeFunction, weightedSum_partialWeights] at hv
    exact hv.symm

theorem finite_nonnegative_polynomial_growth {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (e : ι → ℕ) (ha : ∀ i, 0 ≤ a i)
    (hpos : 0 < ∑ i, a i) :
    ∃ j, 0 < a j ∧ (∀ i, a i ≠ 0 → e i ≤ e j) ∧
      ∀ t : ℝ, 1 ≤ t →
        a j * t ^ e j ≤ ∑ i, a i * t ^ e i ∧
          (∑ i, a i * t ^ e i) ≤ (∑ i, a i) * t ^ e j := by
  first
  | classical
    let S : Finset ι := Finset.univ.filter (fun i => a i ≠ 0)
    have hS : S.Nonempty := by
      first
      | by_contra h
        have hz : ∀ i, a i = 0 := by
          first
          | intro i
            by_contra hi
            exact h ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
        simp only [hz, Finset.sum_const_zero, lt_self_iff_false] at hpos
    obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image S e hS
    have hjpos : 0 < a j := lt_of_le_of_ne (ha j)
      (Ne.symm (Finset.mem_filter.mp hj).2)
    have hle (i : ι) (hi : a i ≠ 0) : e i ≤ e j :=
      hmax i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
    refine ⟨j, hjpos, hle, ?_⟩
    intro t ht
    have ht0 : 0 ≤ t := zero_le_one.trans ht
    constructor
    · exact Finset.single_le_sum (fun i _ => mul_nonneg (ha i) (pow_nonneg ht0 _))
        (Finset.mem_univ j)
    · calc
        (∑ i, a i * t ^ e i) ≤ ∑ i, a i * t ^ e j := by
          first
          | apply Finset.sum_le_sum
            intro i _
            by_cases hi : a i = 0
            · simp only [hi, zero_mul, le_refl]
            · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (hle i hi)) (ha i)
        _ = (∑ i, a i) * t ^ e j := (Finset.sum_mul ..).symm

/-- Lemma 2.1, expressed without a convention for the maximum of an empty
support: a positive coefficient attains the affine dimension, and every other
nonzero coefficient has no larger partial exponent. -/
theorem degree_dimension {n d : ℕ} {K : Fin n → Body d}
    {c : Coefficients n d} (h : Realizes K c)
    (hfull : 0 < bodyVolume (∑ i, K i)) (I : Finset (Fin n)) :
    ∃ α : MultiIndex n d, 0 < c α ∧
      partialExponent I α = affineDimension (partialBodySum K I) ∧
      ∀ β : MultiIndex n d, c β ≠ 0 →
        partialExponent I β ≤ affineDimension (partialBodySum K I) := by
  first
  | have hc : ∀ α, 0 ≤ c α := Realizes.coefficients_nonnegative h
    have hsum : 0 < ∑ α, c α := h.sum_coefficients.symm ▸ hfull
    obtain ⟨α, hα, hmax, hgrowth⟩ := finite_nonnegative_polynomial_growth c
      (partialExponent I) hc hsum
    have hfull' : 0 < bodyVolume (partialBodySum K I + partialBodySum K Iᶜ) := by
      first
      | rwa [partialBodySum_add_compl]
    have hdim : affineDimension (partialBodySum K I) = partialExponent I α :=
      affineDimension_eq_of_growth (partialBodySum K I) (partialBodySum K Iᶜ)
        hfull' hα (by
          intro t ht
          rw [Realizes.partial_volume_formula h I (zero_le_one.trans ht)]
          exact hgrowth t ht)
    exact ⟨α, hα, hdim.symm, fun β hβ => (hmax β hβ).trans_eq hdim.symm⟩

/-- The paper's hypothesis of a full-dimensional total body, stated literally
as equality of its affine span with the ambient affine space. -/
theorem lemma_2_1 {n d : ℕ} {K : Fin n → Body d} {c : Coefficients n d}
    (h : Realizes K c)
    (hfull : affineSpan ℝ ((∑ i, K i : Body d) : Set (Space d)) = ⊤)
    (I : Finset (Fin n)) (_hI : I.Nonempty) :
    ∃ α : MultiIndex n d, 0 < c α ∧
      partialExponent I α = affineDimension (partialBodySum K I) ∧
      ∀ β : MultiIndex n d, c β ≠ 0 →
        partialExponent I β ≤ affineDimension (partialBodySum K I) := by
  first
  | exact degree_dimension h (Iff.mpr (bodyVolume_pos_iff_affineSpan_eq_top _) hfull) I

theorem degree_dimension_eq_of_support_bound {n d m : ℕ} {K : Fin n → Body d}
    {c : Coefficients n d} (h : Realizes K c) (I : Finset (Fin n))
    (hupper : ∀ β : MultiIndex n d, c β ≠ 0 → partialExponent I β ≤ m)
    (hlower : ∃ α : MultiIndex n d, 0 < c α ∧ partialExponent I α = m) :
    affineDimension (partialBodySum K I) = m := by
  first
  | obtain ⟨α, hα, heα⟩ := hlower
    have hc := Realizes.coefficients_nonnegative h
    have hsum : 0 < ∑ β, c β := lt_of_lt_of_le hα
      (Finset.single_le_sum (fun β _ => hc β) (Finset.mem_univ α))
    have hfull : 0 < bodyVolume (∑ i, K i) := h.sum_coefficients ▸ hsum
    obtain ⟨β, hβ, heβ, hmax⟩ := degree_dimension h hfull I
    apply le_antisymm
    · rw [← heβ]
      exact hupper β hβ.ne'
    · rw [← heα]
      exact hmax α hα.ne'

end VolumePolynomials

module

public import PaperVerification.AlternatingFormsStraightening
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action

/-!
# Weighted Boolean inclusion maps

Diagonal scaling transports the explicit central Boolean inverse to every
choice of nonzero coefficients.  These are the actual coefficient maps for
multiplication by a weighted linear form in the square-zero polynomial algebra.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms

open scoped BigOperators

variable {K ι : Type*} [Fintype ι] [DecidableEq ι]

def subsetWeight [CommRing K] (a : ι → K) (S : Finset ι) : K := ∏ i ∈ S, a i

theorem subsetWeight_ne_zero [Field K] (a : ι → K) (ha : ∀ i, a i ≠ 0) (S : Finset ι) :
    subsetWeight a S ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun i hi ↦ ha i)

theorem subsetWeight_erase [Field K] (a : ι → K) (S : Finset ι) (i : S) :
    a i.val * subsetWeight a (S.erase i.val) = subsetWeight a S := by
  exact Finset.mul_prod_erase S a i.property

def weightedInclusionOperator [CommRing K] (a : ι → K) (n : ℕ) :
    (FixedSubsets ι n → K) →ₗ[K] (FixedSubsets ι (n+1) → K) where
  toFun v U := ∑ i : U.val, a i.val * v (eraseSubset U i)
  map_add' v w := by ext U; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c v := by ext U; simp [Finset.mul_sum, mul_left_comm]

def subsetWeightEquiv [Field K] (a : ι → K) (ha : ∀ i, a i ≠ 0) (n : ℕ) :
    (FixedSubsets ι n → K) ≃ₗ[K] (FixedSubsets ι n → K) where
  toFun v U := subsetWeight a U.val * v U
  invFun v U := (subsetWeight a U.val)⁻¹ * v U
  left_inv v := by
    ext U
    change (subsetWeight a U.val)⁻¹ * (subsetWeight a U.val * v U) = v U
    rw [← mul_assoc, inv_mul_cancel₀ (subsetWeight_ne_zero a ha U.val), one_mul]
  right_inv v := by
    ext U
    change subsetWeight a U.val * ((subsetWeight a U.val)⁻¹ * v U) = v U
    rw [← mul_assoc, mul_inv_cancel₀ (subsetWeight_ne_zero a ha U.val), one_mul]
  map_add' v w := by ext U; exact mul_add _ _ _
  map_smul' c v := by ext U; exact mul_left_comm _ _ _

theorem weightedInclusion_conjugate [Field K] (a : ι → K) (ha : ∀ i, a i ≠ 0)
    (n : ℕ) (v : FixedSubsets ι n → K) :
    weightedInclusionOperator a n (subsetWeightEquiv a ha n v) =
      subsetWeightEquiv a ha (n+1) (inclusionOperator n v) := by
  ext U
  change (∑ i : U.val, a i.val * (subsetWeight a (U.val.erase i.val) *
    v (eraseSubset U i))) = subsetWeight a U.val *
      ∑ i : U.val, v (eraseSubset U i)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← mul_assoc, subsetWeight_erase]

theorem weightedInclusion_surjective [Field K] [CharZero K] (a : ι → K)
    (ha : ∀ i, a i ≠ 0) (n : ℕ) (hι : Fintype.card ι = 2*n+1) :
    Function.Surjective (weightedInclusionOperator a n) := by
  intro v
  obtain ⟨u, hu⟩ := inclusionOperator_surjective (K := K) n hι
    ((subsetWeightEquiv a ha (n+1)).symm v)
  refine ⟨subsetWeightEquiv a ha n u, ?_⟩
  rw [weightedInclusion_conjugate, hu, LinearEquiv.apply_symm_apply]

theorem weightedInclusion_injective [Field K] [CharZero K] (a : ι → K)
    (ha : ∀ i, a i ≠ 0) (n : ℕ) (hι : Fintype.card ι = 2*n+1) :
    Function.Injective (weightedInclusionOperator a n) := by
  intro u v huv
  obtain ⟨u', rfl⟩ := (subsetWeightEquiv a ha n).surjective u
  obtain ⟨v', rfl⟩ := (subsetWeightEquiv a ha n).surjective v
  rw [weightedInclusion_conjugate, weightedInclusion_conjugate] at huv
  have he := inclusionOperator_injective (K := K) n hι
    ((subsetWeightEquiv a ha (n+1)).injective huv)
  exact congrArg (subsetWeightEquiv a ha n) he

/-- The explicit weighted inverse in every commutative square-zero algebra.
The coefficient is `b_T / b_P`, which is the orientation needed for the
superincreasing-parameter argument. -/
theorem weighted_local_pair_division [Field K] [CharZero K]
    {A : Type*} [CommRing A] [Algebra K A]
    (a : ι → K) (ha : ∀ i, a i ≠ 0) (y : ι → A)
    (hy : ∀ i, y i * y i = 0) (n : ℕ)
    (hι : Fintype.card ι = 2*n+1) (P : FixedSubsets ι (n+1)) :
    (∑ i, a i • y i) *
        (∑ T : FixedSubsets ι n,
          (inverseCoefficient (K := K) n (T.val ∩ P.val).card *
            (subsetWeight a T.val / subsetWeight a P.val)) •
              ∏ i ∈ T.val, y i) = ∏ i ∈ P.val, y i := by
  have hz (i : ι) : (a i • y i) * (a i • y i) = 0 := by
    rw [smul_mul_assoc, mul_smul_comm, hy, smul_zero, smul_zero]
  have hprod (S : Finset ι) :
      (∏ i ∈ S, a i • y i) = subsetWeight a S • ∏ i ∈ S, y i :=
    Finset.prod_smul S a y
  have h := local_pair_division (K := K) (fun i ↦ a i • y i) hz n hι P
  simp_rw [hprod] at h
  have hh := congrArg (fun z : A ↦ (subsetWeight a P.val)⁻¹ • z) h
  rw [← mul_smul_comm, smul_smul,
    inv_mul_cancel₀ (subsetWeight_ne_zero a ha P.val), one_smul] at hh
  rw [← hh]
  congr 1
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  simp only [smul_smul, div_eq_mul_inv]
  congr 1
  ring

end PaperVerification.AlternatingForms

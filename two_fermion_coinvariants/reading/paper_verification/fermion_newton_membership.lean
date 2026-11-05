module

public import PaperVerification.FermionNewtonTangency
public import PaperVerification.FermionNewtonSaito

/-!
# The literal common-numerator columns belong to the Newton module

The weighted sum of every column is already known to be polynomial. On a
negative hyperplane all rows outside its endpoints are divisible by the
equation, so subtraction from that total contraction proves the remaining
weighted two-row condition. This completes all defining conditions of the
paper's actual module.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Newton

open MvPolynomial
open scoped BigOperators Matrix

variable {F : Type*} [Field F] {n : ℕ}

theorem columnCommonNumerator_weighted_sum
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (hc : Compatible δ σ)
    (hβ : ∀ i, β i ≠ 0) (i : Fin n) :
    (∑ k, C (β k) * columnCommonNumerator β δ σ hc i k) =
      negativeDenominator σ * columnContraction β δ σ i := by
  apply IsFractionRing.injective (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n))
  have hscalar (k : Fin n) : algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)) (C (β k)) =
      algebraMap F (RationalFunctions (F := F) (n := n)) (β k) := by
    rw [← MvPolynomial.algebraMap_eq,
      IsScalarTower.algebraMap_apply F (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n))]
  simp only [map_sum, map_mul, map_columnCommonNumerator, hscalar]
  calc
    (∑ k, algebraMap F (RationalFunctions (F := F) (n := n)) (β k) *
        (algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)) (negativeDenominator σ) *
          newtonColumn β δ σ i k)) =
        algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)) (negativeDenominator σ) *
          ∑ k, algebraMap F (RationalFunctions (F := F) (n := n)) (β k) * newtonColumn β δ σ i k := by
      simp only [Finset.mul_sum, mul_left_comm]
    _ = _ := by rw [newtonColumn_weighted_sum β δ σ i hβ]

theorem columnCommonNumerator_negative_pair_dvd
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (hc : Compatible δ σ)
    (hβ : ∀ i, β i ≠ 0) (i : Fin n) (e : Edge n) (he : σ e.1.1 = -1) :
    edgeLinear e ∣ C (β e.1.1) * columnCommonNumerator β δ σ hc i e.1.1 +
      C (β e.1.2) * columnCommonNumerator β δ σ hc i e.1.2 := by
  let A := columnCommonNumerator β δ σ hc i
  have htotal : edgeLinear e ∣ ∑ k, C (β k) * A k := by
    rw [columnCommonNumerator_weighted_sum β δ σ hc hβ i]
    exact dvd_mul_of_dvd_left (edgeLinear_dvd_negativeDenominator σ e he) _
  have hrest : edgeLinear e ∣
      ∑ k ∈ (Finset.univ.erase e.1.1).erase e.1.2, C (β k) * A k := by
    apply Finset.dvd_sum
    intro k hk
    have hk₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    have hk₂ := (Finset.mem_erase.mp hk).1
    exact dvd_mul_of_dvd_right
      (columnCommonNumerator_negative_other_dvd β δ σ hc i e he k hk₁ hk₂) _
  have hsplit : (∑ k, C (β k) * A k) =
      (∑ k ∈ (Finset.univ.erase e.1.1).erase e.1.2, C (β k) * A k) +
        (C (β e.1.1) * A e.1.1 + C (β e.1.2) * A e.1.2) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ e.1.1),
      ← Finset.sum_erase_add _ _ (show e.1.2 ∈ Finset.univ.erase e.1.1 by simp [ne_of_gt e.2])]
    ring
  have h := dvd_sub htotal hrest
  simpa only [hsplit, add_sub_cancel_left] using h

/-- Every clause of the literal numerator-module definition, for every
explicit Newton column and every compatible profile. -/
theorem commonNumeratorMatrix_column_mem
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (hc : Compatible δ σ)
    (hβ : ∀ i, β i ≠ 0) (i : Fin n) :
    (fun k ↦ commonNumeratorMatrix β δ σ hc k i) ∈ numeratorModule β δ σ := by
  refine ⟨columnCommonNumerator_coordinate_dvd β δ σ hc i, ?_, ?_⟩
  · intro e he
    exact columnCommonNumerator_positive_dvd β δ σ hc i e he
  · intro e he
    exact ⟨columnCommonNumerator_negative_pair_dvd β δ σ hc hβ i e he,
      fun k hka hkb ↦ columnCommonNumerator_negative_other_dvd β δ σ hc i e he k hka hkb⟩

theorem columnContraction_mem_contractionIdeal
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (hc : Compatible δ σ)
    (hβ : ∀ i, β i ≠ 0) (i : Fin n) :
    columnContraction β δ σ i ∈ contractionIdeal β δ σ :=
  ⟨_, commonNumeratorMatrix_column_mem β δ σ hc hβ i,
    columnCommonNumerator_weighted_sum β δ σ hc hβ i⟩

theorem numeratorDetFactor_dvd_commonNumeratorMatrix
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (hc : Compatible δ σ)
    (hβ : ∀ i, β i ≠ 0) :
    numeratorDetFactor δ σ ∣ (commonNumeratorMatrix β δ σ hc).det :=
  numeratorDetFactor_dvd_det β δ σ _ hβ (commonNumeratorMatrix_column_mem β δ σ hc hβ)

end PaperVerification.Fermion.Newton

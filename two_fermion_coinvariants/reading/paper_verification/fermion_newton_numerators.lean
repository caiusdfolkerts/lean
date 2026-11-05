module

public import PaperVerification.FermionNewtonDenominators

/-!
# The common-numerator matrix of the literal Newton columns

The matrix is defined by genuine polynomial representatives after clearing
the full negative denominator. Their existence and coordinate divisibility
are proved from the actual interpolation and residue formulas. Injectivity
of the polynomial embedding makes the representatives unique.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace PaperVerification.Fermion.Newton

open MvPolynomial
open scoped BigOperators Matrix

variable {F : Type*} [Field F] {n : ℕ}

theorem newtonColumn_active_formula
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (i k : Fin n)
    (hk : k ∈ activeInterval δ i) :
    newtonColumn β δ σ i k =
      algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)) ((columnNumerator δ σ i).eval (X k)) /
        algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)) (starDenominator k (earlierNegative σ i)) := by
  rw [newtonColumn, rationalColumn, if_pos hk]
  rw [show rationalNode (F := F) k =
    algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)) (X k) from rfl,
    Polynomial.eval_map_apply, map_starDenominator]
  simp only [Lagrange.nodal, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, rationalNode]

theorem newtonColumn_residue_formula
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (i k : Fin n)
    (hk : k ∈ earlierNegative σ i) :
    newtonColumn β δ σ i k = ∑ l ∈ activeInterval δ i,
      algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)) (C (β l / β k)) *
        (algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)) ((columnNumerator δ σ i).eval (X k)) /
          algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n))
            (starDenominator k ((earlierNegative σ i).erase k) * (X k - X l))) := by
  have hna : k ∉ activeInterval δ i := fun ha ↦
    Finset.disjoint_left.mp (activeInterval_disjoint_earlierNegative δ σ i) ha hk
  rw [newtonColumn, rationalColumn, if_neg hna, if_pos hk, simpleResidue]
  rw [show rationalNode (F := F) k =
    algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)) (X k) from rfl,
    Polynomial.eval_map_apply]
  simp only [Lagrange.nodalWeight, Finset.prod_inv_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  have hC (a : F) :
      algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)) (C a) =
        algebraMap F (RationalFunctions (F := F) (n := n)) a :=
    (IsScalarTower.algebraMap_apply F (P (F := F) (n := n))
      (RationalFunctions (F := F) (n := n)) a).symm
  rw [map_mul, map_starDenominator, map_sub, hC, map_div₀]
  simp only [rationalNode, hC, div_eq_mul_inv, mul_inv_rev]
  ring

theorem newtonColumn_mem_cleared_coordinate
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (hc : Compatible δ σ)
    (i k : Fin n) :
    newtonColumn β δ σ i k ∈
      clearedDivisibility (negativeDenominator σ) (X k ^ δ k) := by
  by_cases ha : k ∈ activeInterval δ i
  · rw [newtonColumn_active_formula β δ σ i k ha]
    apply fraction_mem_clearedDivisibility
    · exact active_denominator_dvd δ σ i k ha
    · apply starDenominator_ne_zero
      exact fun hn ↦ Finset.disjoint_left.mp (activeInterval_disjoint_earlierNegative δ σ i) ha hn
    · exact evaluated_numerator_coordinate_dvd δ σ i k
        (activeInterval_multiplicity_le δ i k ha)
  · by_cases hn : k ∈ earlierNegative σ i
    · rw [newtonColumn_residue_formula β δ σ i k hn]
      apply (clearedDivisibility (negativeDenominator σ) (X k ^ δ k)).sum_mem
      intro l hl
      rw [← Algebra.smul_def]
      apply (clearedDivisibility (negativeDenominator σ) (X k ^ δ k)).smul_mem
      apply fraction_mem_clearedDivisibility
      · exact residue_denominator_dvd δ σ i k l hn hl
      · apply mul_ne_zero (starDenominator_ne_zero k _ (Finset.notMem_erase k _))
        have hkl : k < l := ((mem_earlierNegative σ i k).mp hn).1.trans_le
          ((mem_activeInterval δ i l).mp hl).1
        exact sub_ne_zero.mpr (fun h ↦ (ne_of_lt hkl) (MvPolynomial.X_injective h))
      · exact evaluated_numerator_coordinate_dvd δ σ i k
          (earlierNegative_multiplicity_le δ σ hc i k hn)
    · have hz : newtonColumn β δ σ i k = 0 := by
        simp only [newtonColumn, rationalColumn, if_neg ha, if_neg hn]
      rw [hz]
      exact (clearedDivisibility _ _).zero_mem

def columnCommonNumerator
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (hc : Compatible δ σ)
    (i k : Fin n) : P (F := F) (n := n) :=
  Classical.choose (newtonColumn_mem_cleared_coordinate β δ σ hc i k)

theorem columnCommonNumerator_coordinate_dvd
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (hc : Compatible δ σ)
    (i k : Fin n) : X k ^ δ k ∣ columnCommonNumerator β δ σ hc i k :=
  (Classical.choose_spec (newtonColumn_mem_cleared_coordinate β δ σ hc i k)).1

theorem map_columnCommonNumerator
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (hc : Compatible δ σ)
    (i k : Fin n) :
    algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)) (columnCommonNumerator β δ σ hc i k) =
      algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)) (negativeDenominator σ) * newtonColumn β δ σ i k :=
  (Classical.choose_spec (newtonColumn_mem_cleared_coordinate β δ σ hc i k)).2

theorem columnCommonNumerator_unique
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (hc : Compatible δ σ)
    (i k : Fin n) (a : P (F := F) (n := n))
    (ha : algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)) a =
      algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)) (negativeDenominator σ) * newtonColumn β δ σ i k) :
    a = columnCommonNumerator β δ σ hc i k :=
  IsFractionRing.injective (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n))
    (ha.trans (map_columnCommonNumerator β δ σ hc i k).symm)

def commonNumeratorMatrix
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (hc : Compatible δ σ) :
    Matrix (Fin n) (Fin n) (P (F := F) (n := n)) :=
  fun k i ↦ columnCommonNumerator β δ σ hc i k

theorem commonNumeratorMatrix_map
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (hc : Compatible δ σ) :
    (commonNumeratorMatrix β δ σ hc).map (algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n))) =
      algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)) (negativeDenominator σ) •
        (fun k i ↦ newtonColumn β δ σ i k :
          Matrix (Fin n) (Fin n) (RationalFunctions (F := F) (n := n))) := by
  ext k i
  exact map_columnCommonNumerator β δ σ hc i k

theorem commonNumeratorMatrix_det_ne_zero
    (β : Fin n → F) (δ : Fin n → ℕ) (σ : Fin n → ℤ) (hc : Compatible δ σ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)) :
    (commonNumeratorMatrix β δ σ hc).det ≠ 0 := by
  have hq : algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)) (negativeDenominator σ) ≠ 0 := by
    intro hz
    exact negativeDenominator_ne_zero σ
      (IsFractionRing.injective (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n)) (by simpa using hz))
  intro hz
  have h := congrArg (algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n))) hz
  rw [map_zero, ← matrix_map_det,
    commonNumeratorMatrix_map, Matrix.det_smul, Fintype.card_fin] at h
  exact (mul_ne_zero (pow_ne_zero n hq) (newtonColumn_det_ne_zero F n δ σ β hc hσ hβ)) h

end PaperVerification.Fermion.Newton

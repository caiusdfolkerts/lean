module

public import PaperVerification.FermionNewtonMonicContractions

/-!
# The unchanged comparison matrix for an arbitrary monic polynomial

The zero-profile comparison matrix is polynomial and has determinant a
nonzero scalar times the exact difference product. Multiplying its rows
by evaluations of `G` preserves the comparison identity. The determinant
colon theorem then applies to the actual regular moment sequence.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.Fermion.Newton

open MvPolynomial
open scoped BigOperators Matrix

variable {F : Type*} [Field F] {n : ℕ}

 theorem newtonColumn_constant_row_scaling
    (β : Fin n → F) (d : ℕ) (σ : Fin n → ℤ) (i k : Fin n) :
    newtonColumn β (fun _ ↦ d) σ i k =
      rationalNode k ^ d * newtonColumn β (fun _ ↦ 0) σ i k := by
  rw [newtonColumn_eq_profileNewtonMatrix F, newtonColumn_eq_profileNewtonMatrix F]
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) (RationalFunctions (F := F) (n := n)) ↦ M k i)
    (profileNewtonMatrix_constant_row_scaling d σ (rationalNode (F := F))
      (fun j ↦ algebraMap F (RationalFunctions (F := F) (n := n)) (β j)))
  simpa only [Matrix.diagonal_mul] using h

 theorem zeroComparison_rational_identity
    (β : Fin n → F) (σ : Fin n → ℤ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)) (j k : Fin n) :
    (∑ i, newtonColumn β (fun _ ↦ 0) σ i k *
      algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n))
        (ordinaryComparisonMatrix β 0 σ hσ hβ i j)) = rationalNode k ^ j.val := by
  let A := algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n))
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) (P (F := F) (n := n)) ↦ A (M k j))
    (numeratorMatrix_mul_ordinaryComparison β 0 σ hσ hβ)
  simp only [Matrix.mul_apply, Matrix.of_apply, map_sum, map_mul, commonNumeratorMatrix,
    zero_add, map_pow] at h
  have hden : A (negativeDenominator σ) ≠ 0 := by
    intro hz
    apply negativeDenominator_ne_zero (F := F) σ
    apply IsFractionRing.injective (P (F := F) (n := n))
      (RationalFunctions (F := F) (n := n))
    simpa only [map_zero] using hz
  apply mul_left_cancel₀ hden
  calc
    _ = ∑ i, (A (negativeDenominator σ) *
        newtonColumn β (fun _ ↦ 0) σ i k) *
          A (ordinaryComparisonMatrix β 0 σ hσ hβ i j) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ ↦ (mul_assoc _ _ _).symm)
    _ = ∑ i, A (columnCommonNumerator β (fun _ ↦ 0) σ
        (compatible_constant 0 σ) i k) *
          A (ordinaryComparisonMatrix β 0 σ hσ hβ i j) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact congrArg (fun z : RationalFunctions (F := F) (n := n) ↦
        z * A (ordinaryComparisonMatrix β 0 σ hσ hβ i j))
          (map_columnCommonNumerator β (fun _ ↦ 0) σ
            (compatible_constant 0 σ) i k).symm
    _ = _ := by simpa only [A, rationalNode] using h

 theorem zeroComparison_constant_contraction
    (β : Fin n → F) (d : ℕ) (σ : Fin n → ℤ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)) (j : Fin n) :
    (∑ i, ordinaryComparisonMatrix β 0 σ hσ hβ i j * columnContraction β (fun _ ↦ d) σ i) =
      powerMoment (fun _ ↦ 1) β d j := by
  let A := algebraMap (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n))
  let B := algebraMap F (RationalFunctions (F := F) (n := n))
  have hC (c : F) : A (C c) = B c := by
    simpa only [A, B, MvPolynomial.algebraMap_eq] using
      (IsScalarTower.algebraMap_apply F (P (F := F) (n := n))
        (RationalFunctions (F := F) (n := n)) c).symm
  have hrow (k : Fin n) :
      (∑ i, A (ordinaryComparisonMatrix β 0 σ hσ hβ i j) *
        newtonColumn β (fun _ ↦ d) σ i k) = rationalNode k ^ (d + j.val) := by
    calc
      _ = ∑ i, A (ordinaryComparisonMatrix β 0 σ hσ hβ i j) *
          (rationalNode k ^ d * newtonColumn β (fun _ ↦ 0) σ i k) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact congrArg (fun z : RationalFunctions (F := F) (n := n) ↦
          A (ordinaryComparisonMatrix β 0 σ hσ hβ i j) * z)
            (newtonColumn_constant_row_scaling β d σ i k)
      _ = rationalNode k ^ d * (∑ i, newtonColumn β (fun _ ↦ 0) σ i k *
          A (ordinaryComparisonMatrix β 0 σ hσ hβ i j)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ ↦ by ring)
      _ = _ := by rw [zeroComparison_rational_identity β σ hσ hβ j k, ← pow_add]
  apply IsFractionRing.injective (P (F := F) (n := n)) (RationalFunctions (F := F) (n := n))
  change A _ = A _
  rw [map_sum]
  simp only [map_mul]
  calc
    _ = ∑ i, A (ordinaryComparisonMatrix β 0 σ hσ hβ i j) *
        (∑ k, B (β k) * newtonColumn β (fun _ ↦ d) σ i k) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact congrArg (fun z : RationalFunctions (F := F) (n := n) ↦
        A (ordinaryComparisonMatrix β 0 σ hσ hβ i j) * z)
          (newtonColumn_weighted_sum β (fun _ ↦ d) σ i
            (singleton_weight_ne_zero β hβ)).symm
    _ = ∑ k, B (β k) * (∑ i, A (ordinaryComparisonMatrix β 0 σ hσ hβ i j) *
        newtonColumn β (fun _ ↦ d) σ i k) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      exact Finset.sum_congr rfl (fun i _ ↦ by dsimp only [B]; ring)
    _ = ∑ k, B (β k) * rationalNode k ^ (d + j.val) := by simp_rw [hrow]
    _ = _ := by simp only [powerMoment, one_mul, map_sum, map_mul, map_pow, hC, rationalNode, A]

 theorem zeroComparison_polynomial_contraction
    (β : Fin n → F) (G : Polynomial F) (σ : Fin n → ℤ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)) (j : Fin n) :
    (∑ i, ordinaryComparisonMatrix β 0 σ hσ hβ i j * polynomialContraction β G σ i) =
      polynomialMoment β G j := by
  classical
  rw [polynomialMoment_eq_coefficientCombination]
  simp only [polynomialContraction, coefficientCombination, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← zeroComparison_constant_contraction β d σ hσ hβ j, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ ↦ by ring)

/-- The literal nonhomogeneous colon ideal, with no supplied comparison,
regularity, colength, or flatness hypothesis. -/
theorem polynomial_principalColon_eq_span_contractions
    (β : Fin n → F) (G : Polynomial F) (hG : G.Monic) (hs : 0 < G.natDegree)
    (σ : Fin n → ℤ) (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)) :
    principalColon (polynomialMomentIdeal β G) (differenceProduct σ) =
      Ideal.span (Set.range (polynomialContraction β G σ)) := by
  let M := ordinaryComparisonMatrix β 0 σ hσ hβ
  have hcomp : Fintype.linearCombination (P (F := F) (n := n)) (polynomialContraction β G σ) ∘ₗ
        Matrix.toLin' M =
      Fintype.linearCombination (P (F := F) (n := n)) (fun j : Fin n ↦ polynomialMoment β G j) := by
    apply (Pi.basisFun (P (F := F) (n := n)) (Fin n)).ext
    intro j
    simp only [LinearMap.comp_apply, Pi.basisFun_apply, Matrix.toLin'_apply,
      Matrix.mulVec_single_one, Fintype.linearCombination_apply_single, one_smul,
      Fintype.linearCombination_apply, smul_eq_mul, Matrix.col_apply]
    simpa only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] using zeroComparison_polynomial_contraction β G σ hσ hβ j
  have hcol := Koszul.span_colon_det_eq_of_isWeaklyRegular
    (polynomialContraction β G σ) (fun j : Fin n ↦ polynomialMoment β G j)
    (Matrix.toLin' M) hcomp (polynomialMoments_isWeaklyRegular β G hG hs hβ)
  rw [LinearMap.det_toLin'] at hcol
  obtain ⟨c, hc, hdet⟩ := exists_ordinaryComparison_determinant_scalar β 0 σ hσ hβ
  change (polynomialMomentIdeal β G).colon {M.det} = _ at hcol
  rw [show M.det = C c * differenceProduct σ from hdet] at hcol
  rw [← hcol]
  ext p
  simp only [mem_principalColon, Submodule.mem_colon_singleton, smul_eq_mul]
  have hu : IsUnit (C c : P (F := F) (n := n)) := (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C
  have h := ((polynomialMomentIdeal β G).unit_mul_mem_iff_mem hu
    (x := p * differenceProduct σ)).symm
  simpa only [mul_left_comm, mul_assoc] using h

end PaperVerification.Fermion.Newton

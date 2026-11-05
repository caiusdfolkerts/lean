module

public import PaperVerification.FermionNewtonNegativeStep
public import PaperVerification.FermionNewtonGenericField

/-!
# The all-one Newton determinant and the full power-expansion assertion

The induction is performed in a faithful tower of rational function fields.
At a negative first sign, the cleared Schur numerator has a nonzero leading
coefficient given by a nonempty prefix sum of the original weights. The
other signs give triangular first-row elimination. The auxiliary expansion
assertion is proved simultaneously, rather than assumed in a determinant
criterion. Finally the result is transported to the paper's literal rational
function field.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace PaperVerification.Fermion.Newton

open Polynomial
open scoped BigOperators Matrix

variable {L : Type*} [Field L] {n : ℕ}

theorem allOne_nonnegative_step_det_ne_zero
    (σ : Fin (n + 1) → ℤ) (x β : Fin (n + 1) → L)
    (hσ : σ 0 = 0 ∨ σ 0 = 1) (hx : Function.Injective x) (hx0 : x 0 ≠ 0)
    (hS : (allOneNewtonMatrix (σ ∘ Fin.succ) (x ∘ Fin.succ) (β ∘ Fin.succ)).det ≠ 0) :
    (allOneNewtonMatrix σ x β).det ≠ 0 := by
  let S := allOneNewtonMatrix (σ ∘ Fin.succ) (x ∘ Fin.succ) (β ∘ Fin.succ)
  rcases hσ with hσ | hσ
  · have hM : allOneNewtonMatrix σ x β = adjoinPowerColumn (x 0) (x ∘ Fin.succ) 0 1 S := by
      rw [allOneNewtonMatrix_eq_adjoin σ x β 1
        (fun k i ↦ by simpa only [Pi.one_apply, one_mul] using
          allOneNewtonMatrix_suffix_flat σ x β hσ k i)]
      congr 1
      funext i
      exact allOneNewtonMatrix_first_row_nonnegative σ x β (by omega) i
    rw [hM, adjoinPowerColumn_zero_row_det]
    simpa only [Pi.one_apply, Finset.prod_const_one, mul_one] using mul_ne_zero hx0 hS
  · have hM : allOneNewtonMatrix σ x β =
        adjoinPowerColumn (x 0) (x ∘ Fin.succ) 0 (fun k ↦ x k.succ - x 0) S := by
      rw [allOneNewtonMatrix_eq_adjoin σ x β (fun k ↦ x k.succ - x 0)
        (allOneNewtonMatrix_suffix_up σ x β hσ)]
      congr 1
      funext i
      exact allOneNewtonMatrix_first_row_nonnegative σ x β (by omega) i
    rw [hM, adjoinPowerColumn_zero_row_det]
    apply mul_ne_zero (mul_ne_zero hx0 _) hS
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    exact sub_ne_zero.mpr (fun he ↦ Fin.succ_ne_zero k (hx he))

variable (F : Type*) [Field F]

/-- The complete simultaneous assertion for every number of variables,
every sign word, and every nonresonant weight family. No height positivity
restriction is required for this determinant assertion. -/
theorem allOneGeneric_det_and_pattern (n : ℕ)
    (σ : Fin n → ℤ) (β : Fin n → F)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)) :
    (allOneNewtonMatrix σ (successiveNode F n) (successiveBaseMap F n ∘ β)).det ≠ 0 ∧
    PowerExpansionPattern (allOneHeight σ)
      (matrixPowerExpansion
        (allOneNewtonMatrix σ (successiveNode F n) (successiveBaseMap F n ∘ β))
        (successiveNode F n)) := by
  induction n with
  | zero =>
      constructor
      · simp only [Matrix.det_isEmpty, ne_eq, one_ne_zero, not_false_eq_true]
      · constructor <;> intro d hd i <;> exact Fin.elim0 i
  | succ n ih =>
      let σs : Fin n → ℤ := σ ∘ Fin.succ
      let βs : Fin n → F := β ∘ Fin.succ
      let y := successiveNode F n
      let γ : Fin n → SuccessiveField F n := successiveBaseMap F n ∘ βs
      let c := suffixCoefficientMap F n
      let φ := newVariablePolynomialMap F n
      let x := successiveNode F (n + 1)
      let γfull : Fin (n + 1) → SuccessiveField F (n + 1) := successiveBaseMap F (n + 1) ∘ β
      have hσs : ∀ i, σs i = -1 ∨ σs i = 0 ∨ σs i = 1 := fun i ↦ hσ i.succ
      have hβs : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, βs i) := by
        intro U hU
        have h := hβ (U.map (Fin.succEmb n)) (hU.map)
        simpa only [Finset.sum_map, Fin.coe_succEmb, βs, Function.comp_apply] using h
      obtain ⟨hdet, hpattern⟩ := ih σs βs hσs hβs
      change (allOneNewtonMatrix σs y γ).det ≠ 0 at hdet
      change PowerExpansionPattern (allOneHeight σs)
        (matrixPowerExpansion (allOneNewtonMatrix σs y γ) y) at hpattern
      have hxsucc : x ∘ Fin.succ = c ∘ y := by
        funext i
        exact successiveNode_succ F n i
      have hγsucc : γfull ∘ Fin.succ = c ∘ γ := by
        funext i
        exact successiveBaseMap_succ F n (β i.succ)
      have hSmap : allOneNewtonMatrix σs (x ∘ Fin.succ) (γfull ∘ Fin.succ) =
          (allOneNewtonMatrix σs y γ).map c := by
        rw [hxsucc, hγsucc, allOneNewtonMatrix_map]
      have hS : (allOneNewtonMatrix σs (x ∘ Fin.succ) (γfull ∘ Fin.succ)).det ≠ 0 := by
        rw [hSmap, matrix_map_det]
        exact (map_ne_zero c).mpr hdet
      have hB : matrixPowerExpansion
          (allOneNewtonMatrix σs (x ∘ Fin.succ) (γfull ∘ Fin.succ)) (x ∘ Fin.succ) =
          fun d i ↦ c (matrixPowerExpansion (allOneNewtonMatrix σs y γ) y d i) := by
        funext d
        rw [hSmap, hxsucc, matrixPowerExpansion_map c _ hdet y d]
        rfl
      have hpatternE : PowerExpansionPattern (allOneHeight σs)
          (matrixPowerExpansion
            (allOneNewtonMatrix σs (x ∘ Fin.succ) (γfull ∘ Fin.succ)) (x ∘ Fin.succ)) := by
        rw [hB]
        exact PowerExpansionPattern.map _ _ hpattern c
      have hM : (allOneNewtonMatrix σ x γfull).det ≠ 0 := by
        rcases hσ 0 with hminus | hnonnegative
        · have hweights : ∀ U : Finset (Fin (n + 1)), U.Nonempty →
              IsUnit (∑ i ∈ U, (Fin.cases (successiveBaseMap F n (β 0)) γ i : SuccessiveField F n)) := by
            intro U hU
            have he : Fin.cases (successiveBaseMap F n (β 0)) γ =
                successiveBaseMap F n ∘ β := by
              funext i
              exact Fin.cases rfl (fun j ↦ rfl) i
            rw [he]
            simp only [Function.comp_apply]
            rw [← map_sum]
            exact (hβ U hU).map (successiveBaseMap F n)
          have hm := allOne_negative_step_det_ne_zero φ (newVariablePolynomialMap_injective F n)
            σs hσs y γ (successiveBaseMap F n (β 0)) hweights hdet hpattern
          have hσcase : σ = Fin.cases (-1) σs := by
            funext i
            exact Fin.cases hminus (fun j ↦ rfl) i
          have hxcase : x = Fin.cases (φ X) (fun i ↦ φ (C (y i))) := by
            funext i
            refine Fin.cases ?_ (fun j ↦ ?_) i
            · exact successiveNode_zero F n
            · exact successiveNode_succ F n j
          have hγcase : γfull =
              Fin.cases (φ (C (successiveBaseMap F n (β 0)))) (fun i ↦ φ (C (γ i))) := by
            funext i
            refine Fin.cases ?_ (fun j ↦ ?_) i
            · exact successiveBaseMap_succ F n (β 0)
            · exact successiveBaseMap_succ F n (β j.succ)
          rw [hσcase, hxcase, hγcase]
          exact hm
        · exact allOne_nonnegative_step_det_ne_zero σ x γfull hnonnegative
            (successiveNode_injective F (n + 1)) (successiveNode_ne_zero F (n + 1) 0) hS
      exact ⟨hM, allOneExpansionPattern_of_suffix σ x γfull (hσ 0)
        (successiveNode_injective F (n + 1)) (successiveNode_ne_zero F (n + 1) 0)
        hM hS hpatternE⟩

def successiveFractionMap (n : ℕ) : RationalFunctions (F := F) (n := n) →+* SuccessiveField F n :=
  IsFractionRing.lift (successiveCoordinateMap_injective F n)

@[simp] theorem successiveFractionMap_node (n : ℕ) (i : Fin n) :
    successiveFractionMap F n (rationalNode i) = successiveNode F n i := by
  exact IsFractionRing.lift_algebraMap (successiveCoordinateMap_injective F n) (MvPolynomial.X i)

@[simp] theorem successiveFractionMap_scalar (n : ℕ) (a : F) :
    successiveFractionMap F n (algebraMap F (RationalFunctions (F := F) (n := n)) a) =
      successiveBaseMap F n a := by
  rw [IsScalarTower.algebraMap_apply F (MvPolynomial (Fin n) F)
    (RationalFunctions (F := F) (n := n)), MvPolynomial.algebraMap_eq]
  exact IsFractionRing.lift_algebraMap (successiveCoordinateMap_injective F n) (MvPolynomial.C a)

/-- Nonvanishing for the actual rational functions of the paper, with no
specialization assumption in the statement. -/
theorem allOneNewtonMatrix_rational_det_ne_zero (n : ℕ)
    (σ : Fin n → ℤ) (β : Fin n → F)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)) :
    (allOneNewtonMatrix σ (rationalNode (F := F))
      (fun i ↦ algebraMap F (RationalFunctions (F := F)) (β i))).det ≠ 0 := by
  have h := (allOneGeneric_det_and_pattern F n σ β hσ hβ).1
  intro hz
  apply h
  have he := congrArg (successiveFractionMap F n) hz
  rw [map_zero, ← matrix_map_det, allOneNewtonMatrix_map] at he
  simpa only [Function.comp_def, successiveFractionMap_node, successiveFractionMap_scalar] using he

theorem activeInterval_constant_eq_activeTail (d : ℕ) (i : Fin n) :
    activeInterval (fun _ : Fin n ↦ d) i = activeTail i := by
  ext k
  simp [activeInterval, activeTail]

theorem newtonColumn_one_eq_allOne (β : Fin n → F) (σ : Fin n → ℤ) (i k : Fin n) :
    newtonColumn β (fun _ ↦ 1) σ i k =
      allOneNewtonMatrix σ (rationalNode (F := F))
        (fun j ↦ algebraMap F (RationalFunctions (F := F)) (β j)) k i := by
  simp only [newtonColumn, allOneNewtonMatrix, activeInterval_constant_eq_activeTail,
    columnNumerator, pow_one, Polynomial.map_mul, Polynomial.map_X, Polynomial.map_prod,
    Polynomial.map_sub, Polynomial.map_C, allOneNumerator, Lagrange.nodal, rationalNode]

theorem newtonColumn_one_det_ne_zero (n : ℕ)
    (σ : Fin n → ℤ) (β : Fin n → F)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 0 ∨ σ i = 1)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)) :
    Matrix.det (fun k i : Fin n ↦ newtonColumn β (fun _ ↦ 1) σ i k) ≠ 0 := by
  simp_rw [newtonColumn_one_eq_allOne F]
  exact allOneNewtonMatrix_rational_det_ne_zero F n σ β hσ hβ

end PaperVerification.Fermion.Newton

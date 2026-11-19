module

public import PaperVerification.AlternatingFormsBooleanQuotient
public import PaperVerification.AlternatingFormsBooleanWeighted
import Lean.Elab.Tactic.Omega

/-!
# The actual Boolean relation matrices

For positive degree the relation maps of the ordinary square-zero quotient
are exactly the weighted subset-incidence matrices.  In degree zero the
relation space is zero.  Thus the polynomial presentation and the finite
matrices agree without a positivity restriction hidden in the definition.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.BooleanQuotient

open scoped BigOperators
open MvPolynomial BooleanCoefficients

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
local notation "P" => MvPolynomial ι K

theorem subsetExponent_sub_single (S : Finset ι) (i : ι) :
    subsetExponent S - Finsupp.single i 1 = subsetExponent (S.erase i) := by
  ext j
  by_cases hji : j = i
  · subst j
    by_cases hi : i ∈ S <;> simp [subsetExponent_apply, hi]
  · simp [subsetExponent_apply, Finsupp.single_apply, hji, eq_comm]

theorem relationMap_succ (b : ι → K) (n : ℕ) (p : P) :
    relationMap b (n + 1) p = weightedInclusionOperator b n (coefficients n p) := by
  ext U
  change (linearForm b * p).coeff (subsetExponent U.val) =
    ∑ i : U.val, b i.val * p.coeff (subsetExponent (U.val.erase i.val))
  simp only [linearForm, Finset.sum_mul, smul_mul_assoc, coeff_sum, coeff_smul,
    coeff_X_mul', subsetExponent_support, subsetExponent_sub_single, smul_eq_mul,
    mul_ite, mul_zero]
  rw [Finset.sum_ite_mem_eq]
  exact (Finset.sum_coe_sort U.val (fun i => b i * p.coeff (subsetExponent (U.val.erase i)))).symm

theorem relationMap_succ_eq (b : ι → K) (n : ℕ) :
    relationMap b (n + 1) = (weightedInclusionOperator b n).comp (coefficients n) := by
  apply LinearMap.ext
  intro p
  ext U
  exact congrFun (relationMap_succ b n p) U

theorem relationMap_range_succ (b : ι → K) (n : ℕ) :
    (relationMap b (n + 1)).range = (weightedInclusionOperator b n).range := by
  ext w
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨coefficients n p, (relationMap_succ b n p).symm⟩
  · rintro ⟨v, rfl⟩
    refine ⟨evaluation n v, ?_⟩
    rw [relationMap_succ, coefficients_evaluation]

theorem relations_succ (b c : ι → K) (n : ℕ) :
    relations b c (n + 1) =
      (weightedInclusionOperator b n).range ⊔ (weightedInclusionOperator c n).range := by
  rw [relations, relationMap_range_succ, relationMap_range_succ]

theorem relationMap_zero (b : ι → K) : relationMap b 0 = 0 := by
  apply LinearMap.ext
  intro p
  ext U
  have hU : U.val = ∅ := Finset.card_eq_zero.mp U.property
  change (linearForm b * p).coeff (subsetExponent U.val) = 0
  simp only [linearForm, Finset.sum_mul, smul_mul_assoc, coeff_sum, coeff_smul,
    coeff_X_mul', subsetExponent_support, hU, Finset.notMem_empty, if_false,
    smul_zero, Finset.sum_const_zero]

theorem relations_zero (b c : ι → K) : relations b c 0 = ⊥ := by
  simp only [relations, relationMap_zero, LinearMap.range_zero, sup_idem]

/-- Degree n+1 of the original quotient, expressed using the two finite matrices. -/
def weightedCokernelEquivPiece (b c : ι → K) (n : ℕ) :
    ((FixedSubsets ι (n + 1) → K) ⧸
      ((weightedInclusionOperator b n).range ⊔ (weightedInclusionOperator c n).range)) ≃ₗ[K]
      piece b c (n + 1) :=
  (Submodule.quotEquivOfEq _ _ (relations_succ b c n).symm).trans
    (cokernelEquivPiece b c (n + 1))

section Evaluation

variable {A : Type*} [CommRing A] [Algebra K A]

theorem aeval_evaluation (y : ι → A) (q : ℕ) (v : FixedSubsets ι q → K) :
    MvPolynomial.aeval y (evaluation q v) = squarefreeEvaluation y q v := by
  change MvPolynomial.aeval y (∑ U : FixedSubsets ι q, v U • subsetMonomial U.val) = _
  rw [map_sum]
  simp only [map_smul, subsetMonomial_eq_prod, map_prod, MvPolynomial.aeval_X,
    squarefreeEvaluation, LinearMap.coe_mk, AddHom.coe_mk]

theorem aeval_squareIdeal_eq_zero (y : ι → A) (hy : ∀ i, y i * y i = 0)
    {p : P} (hp : p ∈ squareIdeal) : MvPolynomial.aeval y p = 0 := by
  have hle : squareIdeal (K := K) (ι := ι) ≤ RingHom.ker (MvPolynomial.aeval y).toRingHom := by
    apply Ideal.span_le.mpr
    rintro p ⟨i, rfl⟩
    change MvPolynomial.aeval y ((X i : P) ^ 2) = 0
    rw [map_pow, MvPolynomial.aeval_X, pow_two]
    exact hy i
  exact hle hp

/-- The weighted incidence matrix acts by actual multiplication in every
commutative algebra of square-zero elements, including zero weights. -/
theorem squarefreeEvaluation_weighted_inclusion (y : ι → A)
    (hy : ∀ i, y i * y i = 0) (b : ι → K) (n : ℕ) (v : FixedSubsets ι n → K) :
    (∑ i, b i • y i) * squarefreeEvaluation y n v =
      squarefreeEvaluation y (n + 1) (weightedInclusionOperator b n v) := by
  have hh : (linearForm b * evaluation n v).IsHomogeneous (n + 1) := by
    simpa only [Nat.add_comm 1 n] using
      (linearForm_isHomogeneous b).mul (evaluation_isHomogeneous n v)
  have hr := homogeneous_reduction_mem (n + 1) (linearForm b * evaluation n v) hh
  have hz := aeval_squareIdeal_eq_zero y hy hr
  rw [map_sub, sub_eq_zero] at hz
  have hcoeff : coefficients (n + 1) (linearForm b * evaluation n v) =
      weightedInclusionOperator b n v := by
    change relationMap b (n + 1) (evaluation n v) = _
    rw [relationMap_succ, coefficients_evaluation]
  rw [hcoeff, aeval_evaluation, map_mul, aeval_evaluation] at hz
  have hl : MvPolynomial.aeval y (linearForm b) = ∑ i, b i • y i := by
    simp only [linearForm, map_sum, map_smul, MvPolynomial.aeval_X]
  simpa only [hl] using hz.symm

end Evaluation

end PaperVerification.AlternatingForms.BooleanQuotient

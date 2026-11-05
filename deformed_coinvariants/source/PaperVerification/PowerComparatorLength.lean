module

public import PaperVerification.PowerRegularComparator
public import PaperVerification.FermionRadical
public import PaperVerification.FermionCompleteIntersectionLength

/-!
# The actual complete homogeneous comparator and its length

The quotient is finite over every ground field. This follows from the proved
common-zero theorem over an algebraic closure and faithful descent of radical
membership, applied to each actual coordinate variable. Its dimension is then
the regular-sequence degree product, with the full natural grading retained.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial
open scoped BigOperators

namespace PaperVerification.PowerOperators

variable {K : Type*} [Field K] {n : ℕ}

abbrev completeHomogeneousIdeal (K : Type*) [Field K] (n m : ℕ) :
    Ideal (MvPolynomial (Fin n) K) :=
  ordinaryFamilyIdeal (completeHomogeneousFamily K n m)

theorem completeHomogeneous_variable_mem_radical (m : ℕ) (hm : 0 < m) (i : Fin n) :
    X i ∈ (completeHomogeneousIdeal K n m).radical := by
  let L := AlgebraicClosure K
  let I := completeHomogeneousIdeal K n m
  let φ : MvPolynomial (Fin n) K →+* MvPolynomial (Fin n) L :=
    MvPolynomial.map (algebraMap K L)
  have hrad : HomogeneousLocalization.originIdeal (K := L) (ι := Fin n) ≤
      (I.map φ).radical := by
    apply HomogeneousLocalization.origin_le_radical_of_zeroLocus
    intro x hx
    apply complete_homogeneous_common_zero hm x
    intro j
    have hmem : φ (MvPolynomial.hsymm (Fin n) K (m+j.val)) ∈ I.map φ :=
      Ideal.mem_map_of_mem φ (Ideal.subset_span ⟨j,rfl⟩)
    have hz := hx _ hmem
    simpa only [φ,MvPolynomial.map_hsymm,MvPolynomial.aeval_eq_eval] using hz
  have hXi : φ (X i) ∈ HomogeneousLocalization.originIdeal (K := L) (ι := Fin n) := by
    change constantCoeff (MvPolynomial.map (algebraMap K L) (X i)) = 0
    simp only [MvPolynomial.map_X,MvPolynomial.constantCoeff_X]
  have hmem : X i ∈ ((I.map φ).radical).comap φ := hrad hXi
  simpa only [φ,AlternatingForms.radical_comap_map_coefficientExtension] using hmem

theorem completeHomogeneous_quotient_finite (m : ℕ) (hm : 0 < m) :
    Module.Finite K (MvPolynomial (Fin n) K ⧸ completeHomogeneousIdeal K n m) := by
  apply Fermion.finite_quotient_of_univariate_radical _
    (fun _ : Fin n => (Polynomial.X : Polynomial K)) (fun _ => Polynomial.monic_X)
  intro i
  simpa only [Polynomial.aeval_X] using completeHomogeneous_variable_mem_radical (K := K) m hm i

theorem completeHomogeneous_quotient_finrank (m : ℕ) (hm : 0 < m) :
    Module.finrank K (MvPolynomial (Fin n) K ⧸ completeHomogeneousIdeal K n m) =
      ∏ i : Fin n, (m+i.val) := by
  letI : Module.Finite K
      (MvPolynomial (Fin n) K ⧸ Ideal.span (Set.range (completeHomogeneousFamily K n m))) :=
    completeHomogeneous_quotient_finite (K := K) (n := n) m hm
  exact GradedHilbert.homogeneous_complete_intersection_finrank
    (completeHomogeneousFamily K n m) (fun i => m+i.val)
    (fun i => MvPolynomial.isHomogeneous_hsymm (m+i.val))
    (complete_homogeneous_isWeaklyRegular K n m hm)

/-- The grading is induced from the literal polynomial quotient. -/
def completeHomogeneousGrading (K : Type*) [Field K] (n m : ℕ) :
    TauCeti.InternalGrading K
      (MvPolynomial (Fin n) K ⧸ completeHomogeneousIdeal K n m) ℕ :=
  GradedHilbert.familyGrading (fun _ => 1) (completeHomogeneousFamily K n m)
    (fun i => m+i.val) (fun i => MvPolynomial.isHomogeneous_hsymm (m+i.val))

@[simp] theorem completeHomogeneousGrading_piece (m d : ℕ) :
    (completeHomogeneousGrading K n m).piece d =
      ordinaryQuotientDegree (completeHomogeneousFamily K n m) d := by
  simp only [completeHomogeneousGrading,GradedHilbert.familyGrading,
    GradedHilbert.idealQuotientGrading_piece,
    ordinaryQuotientDegree,completeHomogeneousIdeal,ordinaryFamilyIdeal]
  rfl

end PaperVerification.PowerOperators

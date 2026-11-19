module

public import PaperVerification.AlternatingFormsOnePlaneDegreeCompatibility
public import PaperVerification.HomogeneousIdealPieces

/-!
# Comparison with the original homogeneous Plucker degree

The coordinate-monomial grading used on the one-plane resolution is
proved equal to the images of homogeneous polynomials in the original
Plucker presentation.  This prevents a transported coordinate grading
from silently changing the intended internal degree.

This reconstructed source is uncompiled in the current run.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms.OnePlaneKoszul

open MvPolynomial

universe u
variable (K : Type u) [Field K] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

theorem coordinateEvaluation_eq_quotient_rename :
    aeval (generator K n)=
      (Ideal.Quotient.mkₐ K (matrixPluckerIdeal (K := K) (s := 1) (n := n))).comp
        (MvPolynomial.rename onePlaneIndex) := by
  ext i
  simp only [aeval_X,AlgHom.comp_apply,rename_X]
  rfl

theorem coordinateMonomial_eq_original_class (d : Fin n →₀ ℕ) :
    coordinateMonomial K n d=Ideal.Quotient.mk _
      (MvPolynomial.rename onePlaneIndex (monomial d (1 : K))) := by
  rw [coordinateMonomial_eq_evaluation,coordinateEvaluation_eq_quotient_rename]
  rfl

def originalDegree (N : ℕ) : Submodule K (Ring K n) :=
  HomogeneousIdealPieces.piece matrixPluckerIdeal N

theorem coordinateBasis_mem_originalDegree (d : Fin n →₀ ℕ) :
    coordinateBasis K n d∈originalDegree K n d.degree := by
  rw [coordinateBasis_apply,coordinateMonomial_eq_original_class]
  exact ⟨MvPolynomial.rename onePlaneIndex (monomial d (1 : K)),
    (isHomogeneous_monomial (1 : K) rfl).rename_isHomogeneous,rfl⟩

theorem onePlaneIdeal_isHomogeneous :
    (matrixPluckerIdeal (K := K) (s := 1) (n := n)).IsHomogeneous
      (homogeneousSubmodule (PluckerIndex 1 n) K) := by
  rw [onePlane_matrixPluckerIdeal]
  exact Ideal.IsHomogeneous.bot _

/-- The degree used on the coefficient basis is exactly the image of
the original ordinary homogeneous Plucker-polynomial subspace. -/
theorem coefficientDegree_eq_originalDegree (N : ℕ) :
    BasisDegree.piece (coordinateBasis K n) Finsupp.degree N=originalDegree K n N := by
  let G := HomogeneousIdealPieces.grading
    (matrixPluckerIdeal (K := K) (s := 1) (n := n)) (onePlaneIdeal_isHomogeneous K n)
  have hB : ∀ d,coordinateBasis K n d∈G.piece d.degree := by
    intro d
    rw [HomogeneousIdealPieces.grading_piece]
    exact coordinateBasis_mem_originalDegree K n d
  have h := GradedComponentBasis.span_homogeneous_basis_piece G
    (coordinateBasis K n) Finsupp.degree hB N
  have hset : coordinateBasis K n '' {d | d.degree=N}=
      Set.range (fun d : {d : Fin n →₀ ℕ // d.degree=N} ↦ coordinateBasis K n d.val) := by
    ext x
    constructor
    · rintro ⟨d,hd,rfl⟩
      exact ⟨⟨d,hd⟩,rfl⟩
    · rintro ⟨d,rfl⟩
      exact ⟨d.val,d.property,rfl⟩
  rw [BasisDegree.piece_eq_span,hset,h,HomogeneousIdealPieces.grading_piece]
  rfl

end PaperVerification.AlternatingForms.OnePlaneKoszul

module

public import PaperVerification.HomogeneousQuotientProjectivePresentation
public import PaperVerification.ProjectiveIrreducible
public import PaperVerification.OnePlaneProjectiveGeometry

/-!
# The original one-plane Plücker scheme is ordinary projective space

The comparison is induced by the literal one-entry Plücker indices and the
proved zero relation ideal. Both directions preserve the original homogeneous
degree, and the actual projective isomorphism preserves the scalar structure.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.AlternatingForms

open AlgebraicGeometry CategoryTheory MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] [CharZero K]

/-- A one-entry increasing index has exactly one ordinary coordinate. -/
def onePlaneIndexEquiv (n : ℕ) : Fin n ≃ PluckerIndex 1 n where
  toFun := onePlaneIndex
  invFun I := I.val 0
  left_inv _ := rfl
  right_inv := onePlaneIndex_eta

/-- The exact original homogeneous quotient is the free coordinate ring. -/
def onePlanePolynomialAlgEquiv (n : ℕ) :
    (MvPolynomial (PluckerIndex 1 n) K ⧸ matrixPluckerIdeal) ≃ₐ[K]
      MvPolynomial (Fin n) K :=
  ((Ideal.quotientEquivAlgOfEq K onePlane_matrixPluckerIdeal).trans
    (AlgEquiv.quotientBot K _)).trans (renameEquiv K (onePlaneIndexEquiv n).symm)

@[simp] theorem onePlanePolynomialAlgEquiv_mk (n : ℕ)
    (p : MvPolynomial (PluckerIndex 1 n) K) :
    onePlanePolynomialAlgEquiv (K := K) n (Ideal.Quotient.mk _ p) =
      rename (onePlaneIndexEquiv n).symm p := rfl

@[simp] theorem onePlanePolynomialAlgEquiv_symm (n : ℕ)
    (p : MvPolynomial (Fin n) K) :
    (onePlanePolynomialAlgEquiv (K := K) n).symm p =
      Ideal.Quotient.mk _ (rename (onePlaneIndexEquiv n) p) := rfl

theorem onePlanePolynomialAlgEquiv_mem (n d : ℕ)
    (x : MvPolynomial (PluckerIndex 1 n) K ⧸ matrixPluckerIdeal)
    (hx : x ∈ onePlaneOriginalGrading (K := K) n d) :
    onePlanePolynomialAlgEquiv n x ∈ homogeneousSubmodule (Fin n) K d := by
  change x ∈ HomogeneousQuotientProjective.grading _ _ d at hx
  rw [HomogeneousQuotientProjective.grading_eq_piece] at hx
  obtain ⟨p,hp,rfl⟩ := hx
  change rename (onePlaneIndexEquiv n).symm p ∈ homogeneousSubmodule (Fin n) K d
  exact hp.rename_isHomogeneous

theorem onePlanePolynomialAlgEquiv_symm_mem (n d : ℕ)
    (x : MvPolynomial (Fin n) K) (hx : x ∈ homogeneousSubmodule (Fin n) K d) :
    (onePlanePolynomialAlgEquiv n).symm x ∈ onePlaneOriginalGrading (K := K) n d := by
  change _ ∈ HomogeneousQuotientProjective.grading _ _ d
  rw [HomogeneousQuotientProjective.grading_eq_piece]
  exact ⟨rename (onePlaneIndexEquiv n) x,hx.rename_isHomogeneous,rfl⟩

/-- The actual scheme isomorphism retains all original Plücker coordinates. -/
def onePlaneOriginalProjIsoPolynomial (n : ℕ) :
    Proj (onePlaneOriginalGrading (K := K) n) ≅
      Proj (homogeneousSubmodule (Fin n) K) :=
  (projIsoOfGradedAlgEquiv (onePlanePolynomialAlgEquiv n)
    (onePlanePolynomialAlgEquiv_mem n) (onePlanePolynomialAlgEquiv_symm_mem n)).symm

theorem onePlaneOriginalProjIsoPolynomial_hom_over (n : ℕ) :
    (onePlaneOriginalProjIsoPolynomial (K := K) n).hom ≫
      gradedProjStructureMap (homogeneousSubmodule (Fin n) K) =
        onePlaneOriginalStructureMap n :=
  projIsoOfGradedAlgEquiv_inv_over (onePlanePolynomialAlgEquiv n)
    (onePlanePolynomialAlgEquiv_mem n) (onePlanePolynomialAlgEquiv_symm_mem n)

/-- The original one-plane scheme has a genuine closed projective presentation. -/
def onePlaneOriginalProjectivePresentation (n : ℕ) (hn : 0 < n) :
    OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation
      (Proj (onePlaneOriginalGrading (K := ℂ) n)) (onePlaneOriginalStructureMap n) := by
  letI : Nonempty (PluckerIndex 1 n) := ⟨onePlaneIndex ⟨0,hn⟩⟩
  exact HomogeneousQuotientProjective.projectivePresentation
    (matrixPluckerIdeal (s := 1) (n := n))
    (matrixPluckerIdeal_isHomogeneous (by decide : 0 < 1))

/-- The actual original one-plane scheme is irreducible for every nonzero
ambient dimension, by its prime homogeneous quotient. -/
theorem onePlaneOriginalProj_irreducible (n : ℕ) (hn : 0 < n) :
    IrreducibleSpace (Proj (onePlaneOriginalGrading (K := K) n)) := by
  letI := onePlane_ideal_isPrime (K := K) n
  letI := onePlaneOriginalProj_nonempty (K := K) n hn
  exact projective_irreducibleSpace_of_domain _

end PaperVerification.AlternatingForms

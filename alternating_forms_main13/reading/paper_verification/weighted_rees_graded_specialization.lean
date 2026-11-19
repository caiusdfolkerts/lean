module

public import PaperVerification.WeightedReesGradedFibers

/-!
# Graded special-fiber comparison under a proved initial-ideal equality

An equality of the literal initial ideal with a displayed target ideal
preserves the original polynomial grading. This records the precise map
used in both degenerations of the paper.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open MvPolynomial

namespace PaperVerification.WeightedInitialFiber

variable {K σ : Type*} [Field K]
local notation "P" => MvPolynomial σ K
attribute [local instance] MvPolynomial.gradedAlgebra

theorem quotientEquivAlgOfEq_coordinate_piece {Q J : Ideal P} (h : Q = J) (d : ℕ) :
    (HomogeneousIdealPieces.piece Q d).map
      (Ideal.quotientEquivAlgOfEq K h).toLinearEquiv.toLinearMap =
        HomogeneousIdealPieces.piece J d := by
  apply le_antisymm
  · rintro a ⟨x, ⟨p, hp, rfl⟩, rfl⟩
    refine ⟨p, hp, ?_⟩
    exact (Ideal.quotientEquivAlgOfEq_mk K h p).symm
  · rintro a ⟨p, hp, rfl⟩
    refine ⟨Ideal.Quotient.mk Q p, ⟨p, hp, rfl⟩, ?_⟩
    exact Ideal.quotientEquivAlgOfEq_mk K h p

def specialFiberEquivOfInitial (Q : Ideal P) (w : σ → ℕ) (J : Ideal P)
    (h : initialIdeal Q w = J) : ZeroFiber Q w ≃ₐ[K] (P ⧸ J) :=
  (initialQuotientEquiv Q w).symm.trans (Ideal.quotientEquivAlgOfEq K h)

theorem initialQuotientEquiv_symm_coordinate_piece (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) (w : σ → ℕ) (d : ℕ) :
    ((zeroFiberCoordinateGrading Q hQ w).piece d).map
      (initialQuotientEquiv Q w).symm.toLinearEquiv.toLinearMap =
        HomogeneousIdealPieces.piece (initialIdeal Q w) d := by
  have h := GradedAlgebraQuotient.homogeneousEquiv_map_piece
    (zeroFiberCoordinateGrading Q hQ w)
    (HomogeneousIdealPieces.grading (initialIdeal Q w)
      (initialIdeal_coordinate_homogeneous Q hQ w))
    (initialQuotientEquiv Q w).toLinearEquiv.symm
    (initialQuotientEquiv_coordinate_homogeneous Q hQ w).linearEquiv_symm d
  simpa only [HomogeneousIdealPieces.grading_piece, AlgEquiv.toLinearEquiv_symm] using h

/-- The given special-fiber map identifies whole ordinary-coordinate pieces. -/
theorem specialFiberEquivOfInitial_coordinate_piece (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) (w : σ → ℕ) (J : Ideal P)
    (h : initialIdeal Q w = J) (d : ℕ) :
    ((zeroFiberCoordinateGrading Q hQ w).piece d).map
      (specialFiberEquivOfInitial Q w J h).toLinearEquiv.toLinearMap =
        HomogeneousIdealPieces.piece J d := by
  change ((zeroFiberCoordinateGrading Q hQ w).piece d).map
    ((Ideal.quotientEquivAlgOfEq K h).toLinearEquiv.toLinearMap.comp
      (initialQuotientEquiv Q w).symm.toLinearEquiv.toLinearMap) = _
  rw [Submodule.map_comp, initialQuotientEquiv_symm_coordinate_piece,
    quotientEquivAlgOfEq_coordinate_piece]

end PaperVerification.WeightedInitialFiber

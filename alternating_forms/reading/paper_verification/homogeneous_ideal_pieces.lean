module

public import PaperVerification.GradedComponentBasis
public import TauCeti.Algebra.Module.GradedModule.Quotient
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Actual ordinary homogeneous pieces of a polynomial ideal quotient

The grading is inherited from homogeneous polynomial projections and then
transported through the proved module-quotient/ring-quotient comparison.
Its pieces are proved to be the actual images of the homogeneous polynomial
subspaces. A homogeneous basis therefore restricts to these literal pieces.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.HomogeneousIdealPieces

open MvPolynomial

variable {K σ E : Type*} [Field K]
local notation "P" => MvPolynomial σ K
attribute [local instance] MvPolynomial.gradedAlgebra

theorem quotientMap_ker (Q : Ideal P) :
    (Ideal.Quotient.mkₐ K Q).toLinearMap.ker=Q.restrictScalars K := by
  ext p
  exact Ideal.Quotient.eq_zero_iff_mem

def quotientToRingEquiv (Q : Ideal P) : (P⧸Q.restrictScalars K) ≃ₗ[K] (P⧸Q) :=
  (Submodule.quotEquivOfEq _ _ (quotientMap_ker Q).symm).trans
    ((Ideal.Quotient.mkₐ K Q).toLinearMap.quotKerEquivOfSurjective
      (Ideal.Quotient.mkₐ_surjective K Q))

@[simp] theorem quotientToRingEquiv_mk (Q : Ideal P) (p : P) :
    quotientToRingEquiv Q (Submodule.Quotient.mk p)=Ideal.Quotient.mk Q p := by
  simp only [quotientToRingEquiv,LinearEquiv.trans_apply,Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]
  rfl

def piece (Q : Ideal P) (r : ℕ) : Submodule K (P⧸Q) :=
  (homogeneousSubmodule σ K r).map (Ideal.Quotient.mkₐ K Q).toLinearMap

def grading (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) :
    TauCeti.InternalGrading K (P⧸Q) ℕ := by
  let G : TauCeti.InternalGrading K P ℕ :=
    .ofDecomposition (homogeneousSubmodule σ K)
  have hU : DirectSum.SetLike.IsHomogeneous G.piece (Q.restrictScalars K) := by
    rw [TauCeti.InternalGrading.isHomogeneous_ofDecomposition_piece_iff]
    exact hQ
  exact (G.quotient (Q.restrictScalars K) hU).map (quotientToRingEquiv Q)

theorem grading_piece (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) (r : ℕ) :
    (grading Q hQ).piece r=piece Q r := by
  simp only [grading,TauCeti.InternalGrading.map_piece,
    TauCeti.InternalGrading.quotient_piece,TauCeti.InternalGrading.ofDecomposition_piece,
    LinearMap.restrictScalars_self,←Submodule.map_comp]
  have he : (quotientToRingEquiv Q).toLinearMap.comp (Q.restrictScalars K).mkQ=
      (Ideal.Quotient.mkₐ K Q).toLinearMap := by
    apply LinearMap.ext
    intro p
    exact quotientToRingEquiv_mk Q p
  rw [he]
  rfl

def componentBasis (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K))
    (B : Module.Basis E K (P⧸Q)) (degree : E → ℕ)
    (hB : ∀ e,B e∈piece Q (degree e)) (r : ℕ) :
    Module.Basis {e // degree e=r} K (piece Q r) :=
  (GradedComponentBasis.componentBasis (grading Q hQ) B degree
    (fun e => (grading_piece Q hQ (degree e)).symm ▸ hB e) r).map
      (LinearEquiv.ofEq _ _ (grading_piece Q hQ r))

@[simp] theorem componentBasis_coe (Q : Ideal P)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K))
    (B : Module.Basis E K (P⧸Q)) (degree : E → ℕ)
    (hB : ∀ e,B e∈piece Q (degree e)) (r : ℕ) (e : {e // degree e=r}) :
    (componentBasis Q hQ B degree hB r e : P⧸Q)=B e.val := by
  simp only [componentBasis,Module.Basis.map_apply,LinearEquiv.coe_ofEq_apply,
    GradedComponentBasis.componentBasis,Module.Basis.coe_span_apply,Function.comp_apply]

end PaperVerification.HomogeneousIdealPieces

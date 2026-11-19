module

public import Continuation.Divisor.InvariantCurves
public import Continuation.Runtime.LaurentAffineDescent
public import Continuation.Runtime.LaurentProductBaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Affineness detected by an actual torus-action principal open

An affine group scheme has an affine action morphism: its action graph
identifies the action with the product projection.  Combining this fact
with the Laurent principal-open descent theorem gives a criterion expressed
entirely in actual regular sections and their actual pullbacks.

The toric affine-neighbourhood application supplies the displayed polynomial
from the ratios of the Cartier character sections. This module does not
assume that the original scheme, or the selected character open, is affine.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry.GroupAction

/-- The actual action morphism of an affine group scheme is affine. -/
theorem action_isAffineHom {S : Scheme.{u}} (G X : Over S)
    [GrpObj G] [ModObj G X] [IsAffineHom G.hom] :
    IsAffineHom (γ[G,X]).left := by
  let e := (Over.forget S).mapIso (ModObj.actionGraphIso G X)
  haveI : IsAffineHom (snd G X).left := by
    change IsAffineHom (pullback.snd G.hom X.hom)
    exact MorphismProperty.pullback_snd _ _ ‹IsAffineHom G.hom›
  have haction : e.hom ≫ (snd G X).left = (γ[G,X]).left :=
    congrArg (fun f : G ⊗ X ⟶ X => f.left) (ModObj.actionGraphIso_hom_snd G X)
  rw [← haction]
  infer_instance

end AlgebraicGeometry.GroupAction

namespace PaperVerification.ToricSchemes

variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]
    (M : Type) [AddCommGroup M] [UniqueSums M]
    (X : Over (Spec (CommRingCat.of k)))
    [ModObj (splitTorusOver k M) X]
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    (i : X.left ⟶ Spec (CommRingCat.of R))
    (hi : i ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = X.hom)

/-- The actual product comparison for the torus and an affine comparison
of its acted-on scheme. -/
abbrev torusProductAffineComparison :
    (splitTorusOver k M ⊗ X).left ⟶
      Spec (CommRingCat.of (AddMonoidAlgebra R M)) :=
  laurentProductComparison k R M X.hom i hi

/-- If a regular function has affine nonvanishing open and its actual
coaction is represented by a Laurent polynomial with one unit coefficient,
then the acted-on scheme itself is affine. -/
theorem isAffine_of_affine_torus_action_principal
    (r : Γ(X.left, ⊤)) (hr : IsAffineOpen (X.left.basicOpen r))
    (F : AddMonoidAlgebra R M) (m : M) (hm : IsUnit (F.coeff m))
    (hF : (torusProductAffineComparison k R M X i hi).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (AddMonoidAlgebra R M))).inv F) =
      (γ[splitTorusOver k M,X]).left.appTop r) : IsAffine X.left := by
  let G := splitTorusOver k M
  let q := torusProductAffineComparison k R M X i hi
  letI : IsAffineHom G.hom := by
    change IsAffineHom (Spec.map (CommRingCat.ofHom
      (algebraMap k (AddMonoidAlgebra k M))))
    infer_instance
  letI : IsAffineHom (γ[G,X]).left := GroupAction.action_isAffineHom G X
  have hopen : q ⁻¹ᵁ (PrimeSpectrum.basicOpen F :
      (Spec (CommRingCat.of (AddMonoidAlgebra R M))).Opens) =
      (γ[G,X]).left ⁻¹ᵁ X.left.basicOpen r := by
    rw [← basicOpen_eq_of_affine (R := CommRingCat.of (AddMonoidAlgebra R M)) F,
      Scheme.preimage_basicOpen_top, hF, Scheme.preimage_basicOpen_top]
    rfl
  have hD : IsAffineOpen (q ⁻¹ᵁ (PrimeSpectrum.basicOpen F :
      (Spec (CommRingCat.of (AddMonoidAlgebra R M))).Opens)) := by
    rw [hopen]
    exact hr.preimage (γ[G,X]).left
  exact isAffine_of_affine_laurent_principal_preimage R i
    (snd G X).left q (laurentProductComparison_isPullback k R M X.hom i hi)
    F m hm hD

end PaperVerification.ToricSchemes

#print axioms AlgebraicGeometry.GroupAction.action_isAffineHom
#print axioms PaperVerification.ToricSchemes.isAffine_of_affine_torus_action_principal

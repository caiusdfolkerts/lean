module

public import Continuation.Runtime.LaurentProductBaseChange

/-!
# Actual regular coordinates on a Laurent product

The product comparison pulls a Laurent monomial with a regular coefficient
back to the product of the character from the first factor and the regular
coefficient from the second factor. These are identities in the ordinary
global section ring, before passing to a function field.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open AlgebraicGeometry CategoryTheory Limits
open scoped AlgebraMonoidAlgebra

namespace PaperVerification.ToricSchemes

variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]
    (M : Type) [AddCommMonoid M]
    {X : Scheme.{u}} (i : X ⟶ Spec (CommRingCat.of k))
    (η : X ⟶ Spec (CommRingCat.of R))
    (hη : η ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = i)

local notation "a" => Spec.map (CommRingCat.ofHom (algebraMap k (AddMonoidAlgebra k M)))
local notation "τ" => Spec.map (CommRingCat.ofHom (algebraMap
  (AddMonoidAlgebra k M) (AddMonoidAlgebra R M)))
local notation "σ" => Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R M)))

/-- Pullback of actual affine coordinates to actual global sections. -/
def laurentProductSectionMap : AddMonoidAlgebra R M →+* Γ(pullback a i, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (AddMonoidAlgebra R M))).inv ≫
    (laurentProductComparison k R M i η hη).appTop).hom

theorem laurentProductSectionMap_coefficient (r : R) :
    laurentProductSectionMap k R M i η hη
        (algebraMap R (AddMonoidAlgebra R M) r) =
      (pullback.snd a i).appTop
        (η.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) := by
  let q := laurentProductComparison k R M i η hη
  have hs : (σ).appTop ≫ q.appTop = η.appTop ≫ (pullback.snd a i).appTop := by
    rw [← Scheme.Hom.comp_appTop, laurentProductComparison_second,
      Scheme.Hom.comp_appTop]
  have hc : CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R M)) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (AddMonoidAlgebra R M))).inv ≫ q.appTop =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        η.appTop ≫ (pullback.snd a i).appTop := by
    rw [Scheme.ΓSpecIso_inv_naturality_assoc, hs]
  exact congrArg (fun φ => φ r) hc

theorem laurentProductSectionMap_character (b : AddMonoidAlgebra k M) :
    laurentProductSectionMap k R M i η hη
        (algebraMap (AddMonoidAlgebra k M) (AddMonoidAlgebra R M) b) =
      (pullback.fst a i).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (AddMonoidAlgebra k M))).inv b) := by
  let q := laurentProductComparison k R M i η hη
  have hs : (τ).appTop ≫ q.appTop = (pullback.fst a i).appTop := by
    rw [← Scheme.Hom.comp_appTop, laurentProductComparison_first]
  have hc : CommRingCat.ofHom
        (algebraMap (AddMonoidAlgebra k M) (AddMonoidAlgebra R M)) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (AddMonoidAlgebra R M))).inv ≫ q.appTop =
      (Scheme.ΓSpecIso (CommRingCat.of (AddMonoidAlgebra k M))).inv ≫
        (pullback.fst a i).appTop := by
    rw [Scheme.ΓSpecIso_inv_naturality_assoc, hs]
  exact congrArg (fun φ => φ b) hc

/-- A monomial's actual pullback separates its character and coefficient. -/
theorem laurentProductSectionMap_single (m : M) (r : R) :
    laurentProductSectionMap k R M i η hη (AddMonoidAlgebra.single m r) =
      (pullback.snd a i).appTop
          (η.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) *
        (pullback.fst a i).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of (AddMonoidAlgebra k M))).inv
            (AddMonoidAlgebra.single m 1)) := by
  have he : (AddMonoidAlgebra.single m r : AddMonoidAlgebra R M) =
      algebraMap R (AddMonoidAlgebra R M) r *
        algebraMap (AddMonoidAlgebra k M) (AddMonoidAlgebra R M)
          (AddMonoidAlgebra.single m 1) := by
    simp [AddMonoidAlgebra.algebraMap_def, AddMonoidAlgebra.coe_algebraMap]
  rw [he, map_mul, laurentProductSectionMap_coefficient,
    laurentProductSectionMap_character]

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.laurentProductSectionMap_single

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Scalar restriction along a surjective ring homomorphism

Every linear map over the source ring is linear over the quotient: lift
each scalar through the given surjection.  Consequently the actual
extension--restriction adjunction counit is invertible, as is its unit
on every module in the image of restriction.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace ToricPower

universe u v

/-- The inverse on morphisms keeps the underlying additive map unchanged. -/
def restrictScalarsFullyFaithfulOfSurjective
    {R S : Type u} [Ring R] [Ring S] (φ : R →+* S)
    (surjective : Function.Surjective φ) :
    (ModuleCat.restrictScalars.{v} φ).FullyFaithful where
  preimage {M N} f := ModuleCat.ofHom {
    toFun := f
    map_add' := f.hom.map_add
    map_smul' := fun s m => by
      obtain ⟨r, rfl⟩ := surjective s
      exact f.hom.map_smul r m }
  map_preimage f := by ext x; rfl
  preimage_map f := by ext x; rfl

variable {R S : Type u} [CommRing R] [CommRing S]
  (φ : R →+* S) (surjective : Function.Surjective φ)

include surjective

/-- The literal tensor multiplication counit is invertible for every
module over the quotient ring, without finite-generation assumptions. -/
theorem surjectiveScalarCounit_isIso (M : ModuleCat.{u} S) :
    IsIso ((ModuleCat.extendRestrictScalarsAdj φ).counit.app M) := by
  letI := (restrictScalarsFullyFaithfulOfSurjective φ surjective).full
  infer_instance

def surjectiveScalarCounitIso :
    ModuleCat.restrictScalars.{u} φ ⋙ ModuleCat.extendScalars φ ≅
      𝟭 (ModuleCat.{u} S) := by
  letI := (restrictScalarsFullyFaithfulOfSurjective φ surjective).full
  exact asIso (ModuleCat.extendRestrictScalarsAdj φ).counit

/-- The literal adjunction unit is invertible on each restricted module. -/
theorem surjectiveScalarUnit_restricted_isIso (M : ModuleCat.{u} S) :
    IsIso ((ModuleCat.extendRestrictScalarsAdj φ).unit.app
      ((ModuleCat.restrictScalars φ).obj M)) := by
  letI := (restrictScalarsFullyFaithfulOfSurjective φ surjective).full
  infer_instance

end ToricPower

end

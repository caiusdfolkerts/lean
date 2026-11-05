module

public import PaperVerification.SheafCoordinateMorphisms
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Coproduct and product coordinates for finite free sheaves

The canonical map from the free sheaf (defined as a coproduct) to the finite
power of the structure sheaf carries a basis vector to the same coordinate
vector. A section-defined morphism is unchanged by this comparison.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

namespace PaperVerification.SheafFiniteCoordinates

universe u
variable {X : AlgebraicGeometry.Scheme.{u}} {I : Type u} [Fintype I]

/-- The actual coordinate-vector inclusion into the product sheaf. -/
def basisInclusion (i : I) : SheafOfModules.unit X.ringCatSheaf ⟶
    SheafModulePowers.structurePower X I := by
  classical
  exact Pi.lift (fun j => if i = j then 𝟙 _ else 0)

/-- The coproduct universal property gives the comparison with the product. -/
def freeToPower : SheafOfModules.free (R := X.ringCatSheaf) I ⟶
    SheafModulePowers.structurePower X I :=
  Sigma.desc basisInclusion

theorem basisInclusion_fromSections (M : X.Modules) (s : I → M.sections) (i : I) :
    basisInclusion i ≫ SheafCoordinateMorphisms.fromSections M s =
      (SheafOfModules.unitHomEquiv M).symm (s i) := by
  classical
  simp only [SheafCoordinateMorphisms.fromSections, Preadditive.comp_sum,
    ← Category.assoc]
  have hb (j : I) : basisInclusion (X := X) i ≫
      Pi.π (fun _ : I => SheafOfModules.unit X.ringCatSheaf) j =
        (if i = j then 𝟙 _ else 0) := Pi.lift_comp_π _ j
  rw [Finset.sum_eq_single i]
  · exact (congrArg (fun q => q ≫ (SheafOfModules.unitHomEquiv M).symm (s i))
      (hb i)).trans (by simp)
  · intro j hj hji
    exact (congrArg (fun q => q ≫ (SheafOfModules.unitHomEquiv M).symm (s j))
      (hb j)).trans (by simp [Ne.symm hji])
  · simp

/-- Both universal descriptions evaluate the same actual family of sections. -/
theorem freeToPower_fromSections (M : X.Modules) (s : I → M.sections) :
    freeToPower ≫ SheafCoordinateMorphisms.fromSections M s =
      (SheafOfModules.freeHomEquiv M).symm s := by
  apply (SheafOfModules.freeHomEquiv M).injective
  funext i
  change (SheafOfModules.unitHomEquiv M)
      (SheafOfModules.ιFree i ≫ (freeToPower ≫
        SheafCoordinateMorphisms.fromSections M s)) = _
  rw [← Category.assoc]
  change (SheafOfModules.unitHomEquiv M)
      ((Sigma.ι (fun _ : I => SheafOfModules.unit X.ringCatSheaf) i ≫
        Sigma.desc basisInclusion) ≫ SheafCoordinateMorphisms.fromSections M s) = _
  rw [Sigma.ι_desc, basisInclusion_fromSections]
  simp

end PaperVerification.SheafFiniteCoordinates

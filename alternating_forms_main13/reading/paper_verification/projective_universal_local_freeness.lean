module

public import PaperVerification.ProjectiveUniversalQuotient
public import PaperVerification.LocallyFreeOfFrames
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Logic.Equiv.Option

/-!
# The universal kernel is a genuine vector bundle

Every coordinate can serve as the unit pivot. Reindexing the actual finite
power sheaf transports the explicit kernel frame to each standard open.
These frames give native local freeness and finite type for the categorical
kernel of `O^I → O(1)`, over an arbitrary commutative base ring.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

namespace PaperVerification.SheafFiniteCoordinates

universe u
variable {X : Scheme.{u}}

/-- The standard biproduct comparison identifies the actual free sheaf
with the finite power of the structure sheaf. -/
def freePowerIso (I : Type u) [Fintype I] :
    SheafOfModules.free (R := X.ringCatSheaf) I ≅
      SheafModulePowers.structurePower X I := by
  letI : HasBiproduct (fun _ : I => SheafOfModules.unit X.ringCatSheaf) :=
    HasBiproduct.of_hasProduct _
  exact (biproduct.isoCoproduct (fun _ : I => SheafOfModules.unit X.ringCatSheaf)).symm ≪≫
    biproduct.isoProduct (fun _ : I => SheafOfModules.unit X.ringCatSheaf)

/-- Restriction of the same finite power retains its actual free frame. -/
def freeOverPowerIso (I : Type u) [Fintype I] (U : X.Opens) :
    SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅
      (SheafModulePowers.structurePower X I).over U := by
  letI : (SheafOfModules.overFunctor X.ringCatSheaf U).Additive := { map_add := rfl }
  exact SheafOfModules.mapFreeIso (SheafOfModules.overFunctor X.ringCatSheaf U) I (Iso.refl _) ≪≫
    (SheafOfModules.overFunctor X.ringCatSheaf U).mapIso (freePowerIso I)

/-- Coordinate changes act by their actual product projections. -/
def reindexIso (M : X.Modules) {I J : Type u} (e : J ≃ I) :
    SheafModulePowers.power M I ≅ SheafModulePowers.power M J where
  hom := SheafModulePowers.reindex M I J e
  inv := SheafModulePowers.reindex M J I e.symm
  hom_inv_id := by
    apply Pi.hom_ext
    intro i
    simp only [Category.assoc, SheafModulePowers.reindex_projection,
      Equiv.apply_symm_apply, Category.id_comp]
  inv_hom_id := by
    apply Pi.hom_ext
    intro j
    simp only [Category.assoc, SheafModulePowers.reindex_projection,
      Equiv.symm_apply_apply, Category.id_comp]

/-- Reindexing the coordinates and the evaluated sections together leaves
the original sheaf morphism unchanged. -/
theorem reindex_fromSections (M : X.Modules) {I J : Type u}
    [Fintype I] [Fintype J] (e : J ≃ I) (s : I → M.sections) :
    (reindexIso (SheafOfModules.unit X.ringCatSheaf) e).hom ≫
      SheafCoordinateMorphisms.fromSections M (s ∘ e) =
        SheafCoordinateMorphisms.fromSections M s := by
  simp only [SheafCoordinateMorphisms.fromSections, Preadditive.comp_sum,
    ← Category.assoc, reindexIso]
  calc
    _ = ∑ j : J, Pi.π (fun _ : I => SheafOfModules.unit X.ringCatSheaf) (e j) ≫
        (SheafOfModules.unitHomEquiv M).symm (s (e j)) := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun q => q ≫ (SheafOfModules.unitHomEquiv M).symm (s (e j)))
        (SheafModulePowers.reindex_projection
          (SheafOfModules.unit X.ringCatSheaf) I J e j)
    _ = _ := e.sum_comp (fun i =>
      Pi.π (fun _ : I => SheafOfModules.unit X.ringCatSheaf) i ≫
        (SheafOfModules.unitHomEquiv M).symm (s i))

end PaperVerification.SheafFiniteCoordinates

namespace PaperVerification.ProjectiveUniversalQuotient

variable {A σ I : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] [Fintype I] [DecidableEq I]

/-- The actual universal kernel has the frame omitting coordinate `i` on
its corresponding standard open. This includes every finite rank. -/
def kernelFrameAt (a : I → 𝒜 1) (i : I) :
    (kernel (powerQuotient a)).over (Proj.basicOpen 𝒜 (a i : A)) ≅
      (SheafModulePowers.structurePower (Proj 𝒜) {j : I // j ≠ i}).over
        (Proj.basicOpen 𝒜 (a i : A)) := by
  let e := Equiv.optionSubtypeNe i
  let p := SheafFiniteCoordinates.reindexIso
    (SheafOfModules.unit (Proj 𝒜).ringCatSheaf) e
  let k := kernel.mapIso (f := powerQuotient a) (powerQuotient (a ∘ e)) p
    (Iso.refl _) (by
      change powerQuotient a = p.hom ≫ powerQuotient (a ∘ e)
      exact (SheafFiniteCoordinates.reindex_fromSections (Proj.twistingSheaf 𝒜 (1 : ℤ))
          e (fun j => homogeneousSection (a j))).symm)
  exact (SheafOfModules.overFunctor (Proj 𝒜).ringCatSheaf
      (Proj.basicOpen 𝒜 (a i : A))).mapIso k ≪≫ kernelFrameIso (a ∘ e)

/-- The actual free-sheaf frame on each coordinate open. -/
def kernelFreeFrameAt (a : I → 𝒜 1) (i : I) :
    SheafOfModules.free
      (R := (Proj 𝒜).ringCatSheaf.over (Proj.basicOpen 𝒜 (a i : A)))
      {j : I // j ≠ i} ≅
        (kernel (powerQuotient a)).over (Proj.basicOpen 𝒜 (a i : A)) :=
  SheafFiniteCoordinates.freeOverPowerIso _ _ ≪≫ (kernelFrameAt a i).symm

/-- Covering homogeneous coordinates make the genuine universal kernel
locally free in Mathlib's original sense. -/
theorem kernel_isLocallyFree (a : I → 𝒜 1)
    (hcover : (⨆ i, Proj.basicOpen 𝒜 (a i : A)) = ⊤) :
    (kernel (powerQuotient a)).IsLocallyFree :=
  LocallyFreeOfFrames.isLocallyFree _ _ hcover
    (fun i => {j : I // j ≠ i}) (kernelFreeFrameAt a)

/-- The same actual universal kernel is of finite type. -/
theorem kernel_isFiniteType (a : I → 𝒜 1)
    (hcover : (⨆ i, Proj.basicOpen 𝒜 (a i : A)) = ⊤) :
    (kernel (powerQuotient a)).IsFiniteType :=
  LocallyFreeOfFrames.isFiniteType _ _ hcover
    (fun i => {j : I // j ≠ i}) (kernelFreeFrameAt a)

/-- Consequently this kernel has the genuine quasicoherence required
for its relative projectivization. -/
theorem kernel_isQuasicoherent (a : I → 𝒜 1)
    (hcover : (⨆ i, Proj.basicOpen 𝒜 (a i : A)) = ⊤) :
    (kernel (powerQuotient a)).IsQuasicoherent := by
  letI := kernel_isLocallyFree a hcover
  infer_instance

end PaperVerification.ProjectiveUniversalQuotient

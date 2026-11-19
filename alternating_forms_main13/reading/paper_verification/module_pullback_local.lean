/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The unit, restriction, and section constructions below are the corresponding
constructions from TauCeti/AlgebraicGeometry/Modules/Pullback/{Basic,Sections}.
They are placed in a separate namespace and given only their direct Mathlib
imports, so this elementary local argument does not require the independent
tensor-product and quasicoherent-presentation theories. The underlying
pullback, adjunction, and restriction functors remain Mathlib's originals.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Local coordinates for the actual module pullback

These explicit comparison isomorphisms identify a pullback restricted to
an inverse-image open with the pullback of the restricted module. The
section map is the unit of the actual pullback–pushforward adjunction.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.ModulePullbackLocal

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

universe u
variable {X Y : Scheme.{u}}

/-- Pullback preserves the actual structure sheaf. -/
def unitIso (f : X ⟶ Y) :
    (pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  letI : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (pushforward f).IsRightAdjoint
  have h : IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) :=
    SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal _
  @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) h

/-- Restriction of pullback agrees with pullback along the restricted map. -/
def restrictObjIso (f : X ⟶ Y) (V : Y.Opens) (M : Y.Modules) :
    ((pullback f).obj M).restrict (f ⁻¹ᵁ V).ι ≅
      (pullback (f ∣_ V)).obj (M.restrict V.ι) :=
  (restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).app _ ≪≫
    (pullbackComp (f ⁻¹ᵁ V).ι f).app M ≪≫
    (pullbackCongr (morphismRestrict_ι f V).symm).app M ≪≫
    ((pullbackComp (f ∣_ V) V.ι).app M).symm ≪≫
    (pullback (f ∣_ V)).mapIso ((restrictFunctorIsoPullback V.ι).app M).symm

/-- The actual pullback read on the two open slice sites. -/
def overPullback (f : X ⟶ Y) (V : Y.Opens) :
    SheafOfModules (Y.ringCatSheaf.over V) ⥤
      SheafOfModules (X.ringCatSheaf.over (f ⁻¹ᵁ V)) :=
  (overEquiv V).functor ⋙ pullback (f ∣_ V) ⋙ (overEquiv (f ⁻¹ᵁ V)).inverse

/-- The slice-site pullback preserves the structure sheaf. -/
def overUnitIso (f : X ⟶ Y) (V : Y.Opens) :
    SheafOfModules.unit _ ≅ (overPullback f V).obj (SheafOfModules.unit _) :=
  (overEquiv (f ⁻¹ᵁ V)).unitIso.app _ ≪≫
    (overEquiv (f ⁻¹ᵁ V)).inverse.mapIso (unitIso (f ∣_ V)).symm

/-- The slice-site pullback is the restriction of the original pullback. -/
def overObjIso (f : X ⟶ Y) (V : Y.Opens) (M : Y.Modules) :
    (overPullback f V).obj (M.over V) ≅ ((pullback f).obj M).over (f ⁻¹ᵁ V) :=
  ((overEquiv (f ⁻¹ᵁ V)).inverse.mapIso
    ((overFunctorEquiv (f ⁻¹ᵁ V)).app _ ≪≫ restrictObjIso f V M ≪≫
      (pullback (f ∣_ V)).mapIso ((overFunctorEquiv V).app M).symm)).symm ≪≫
    ((overEquiv (f ⁻¹ᵁ V)).unitIso.app _).symm

/-- Pullback of sections is exactly the adjunction unit on that open. -/
def sections (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens) :
    Γ(M, U) →ₛₗ[(f.app U).hom] Γ((pullback f).obj M, f ⁻¹ᵁ U) where
  toFun := ((pullbackPushforwardAdjunction f).unit.app M).app U
  map_add' := map_add _
  map_smul' r s := ((pullbackPushforwardAdjunction f).unit.app M).app_smul r s

/-- Pullback of a section to any open contained in the inverse image. -/
def sectionsLE (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens)
    (V : X.Opens) (hV : V ≤ f ⁻¹ᵁ U) :
    Γ(M, U) →ₛₗ[(f.appLE U V hV).hom] Γ((pullback f).obj M, V) where
  toFun s := ((pullback f).obj M).presheaf.map (homOfLE hV).op (sections f M U s)
  map_add' := by simp
  map_smul' r s := by
    rw [map_smulₛₗ, map_smul]
    rfl

end PaperVerification.ModulePullbackLocal

module

public import PaperVerification.ToricInvertibleFractionalPresentation
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Topology.Sheaves.Module
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.Preserves.Lattice

@[expose] public section

/-!
# Ordinary pullback preserves actual invertible module sheaves

The proof uses the genuine pullback pseudofunctor, the established
equivalence between an open subsite and its open subscheme, and the
ordinary pullback of the structure module. It applies to arbitrary
scheme morphisms, including nondominant closed immersions.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Scheme.Modules

namespace ModuleFrame

variable {X : Scheme.{u}} {M : X.Modules} {U : X.Opens}

/-- The actual open-subscheme version of a frame on the open subsite. -/
def toRestrictIso (e : ModuleFrame M U) :
    M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf :=
  ((overFunctorEquiv U).app M).symm ≪≫
    (overEquiv U).functor.mapIso e ≪≫
      U.sheafOfModulesEquivOverUnit X.ringCatSheaf

/-- Transport a genuine open-subscheme frame back to the open subsite. -/
def ofRestrictIso
    (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    ModuleFrame M U :=
  (overEquiv U).unitIso.app (M.over U) ≪≫
    (overEquiv U).inverse.mapIso ((overFunctorEquiv U).app M ≪≫ e) ≪≫
      U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf

end ModuleFrame

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
/-- The pullback of the actual structure module is the actual structure
module; finality here follows from preservation of the terminal open. -/
def pullbackUnitIso :
    (pullback f).obj (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit Y.ringCatSheaf := by
  letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  letI : Limits.PreservesFiniteLimits (Opens.map f.base) := by
    change Limits.PreservesFiniteLimits (OrderHom.ofClass f.base.frameHom).toFunctor
    infer_instance
  letI : (Opens.map f.base).Final := inferInstance
  letI : IsIso (SheafOfModules.pullbackObjUnitToUnit
      (F := Opens.map f.base) (J := Opens.grothendieckTopology X)
      (K := Opens.grothendieckTopology Y) (S := X.ringCatSheaf)
      (R := Y.ringCatSheaf) f.toRingCatSheafHom) := inferInstance
  exact asIso (SheafOfModules.pullbackObjUnitToUnit
    (F := Opens.map f.base) (J := Opens.grothendieckTopology X)
    (K := Opens.grothendieckTopology Y) (S := X.ringCatSheaf)
    (R := Y.ringCatSheaf) f.toRingCatSheafHom)

namespace ModuleFrame

variable {M : X.Modules} {U : X.Opens} (e : ModuleFrame M U)

/-- The actual pullback frame, with its actual preimage open. -/
def pullbackRestrictIso :
    ((pullback f).obj M).restrict (f ⁻¹ᵁ U).ι ≅
      SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf := by
  let g : (f ⁻¹ᵁ U).toScheme ⟶ U.toScheme := f ∣_ U
  have hg : (f ⁻¹ᵁ U).ι ≫ f = g ≫ U.ι := by
    exact (morphismRestrict_ι f U).symm
  exact
    (restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).app ((pullback f).obj M) ≪≫
    (pullbackComp (f ⁻¹ᵁ U).ι f).app M ≪≫
    (pullbackCongr hg).app M ≪≫
    ((pullbackComp g U.ι).app M).symm ≪≫
    (pullback g).mapIso ((restrictFunctorIsoPullback U.ι).app M).symm ≪≫
    (pullback g).mapIso e.toRestrictIso ≪≫
    pullbackUnitIso g

def pullbackFrame : ModuleFrame ((pullback f).obj M) (f ⁻¹ᵁ U) :=
  ofRestrictIso (pullbackRestrictIso f e)

end ModuleFrame

/-- Pullback preserves genuine local rank one without a dominance,
flatness, smoothness, or integrality assumption on the morphism. -/
theorem isInvertibleModule_pullback {M : X.Modules} (hM : IsInvertibleModule M) :
    IsInvertibleModule ((pullback f).obj M) := by
  intro y
  obtain ⟨U,hy,⟨e⟩⟩ := hM (f y)
  exact ⟨f ⁻¹ᵁ U,hy,⟨ModuleFrame.pullbackFrame f e⟩⟩

/-- On an integral target of pullback, the pulled-back invertible sheaf
therefore has an actual fractional Cartier presentation as well. -/
theorem exists_cartierData_pullback [IsIntegral Y]
    {M : X.Modules} (hM : IsInvertibleModule M) :
    ∃ D : CartierData Y,Nonempty ((pullback f).obj M≅D.sheaf) :=
  exists_cartierData_of_isInvertibleModule _ (isInvertibleModule_pullback f hM)

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.isInvertibleModule_pullback
#print axioms PaperVerification.ToricSchemes.exists_cartierData_pullback

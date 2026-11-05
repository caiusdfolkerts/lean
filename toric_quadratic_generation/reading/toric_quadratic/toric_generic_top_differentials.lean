module

public import PaperVerification.ToricGenericDifferentialSections
public import PaperVerification.ToricExteriorRestriction

@[expose] public section

/-!
# Generic coefficients of the intrinsic top differential sheaf

The map is induced from the actual universal derivation of regular
functions and the ordinary exterior universal property. A chosen basis
of generic differentials only chooses a nonzero rational volume; it
does not prescribe the regular image or its divisor.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open PaperVerification.ToricCharacters
open scoped BaseSections Classical

variable (X : Scheme.{u}) [IsIntegral X] (k : Type u) [CommRing k]
    [X.Over (Spec (CommRingCat.of k))] {n : ℕ}
    (b : Module.Basis (Fin n) X.functionField (KaehlerDifferential k X.functionField))

local notation "ΩX" => differentialSheaf k X
local notation "P" => presheafExteriorPower X.presheaf (SheafOfModules.val (differentialSheaf k X)) n
local notation "K" => X.functionField

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
def genericTopCoefficientValue (U : X.Opens) [Nonempty U] :
    (P).obj (op U)→ₗ[Γ(X,U)]K := by
  letI : Algebra Γ(X,U) K := (X.germToFunctionField U).hom.toAlgebra
  letI : Module Γ(X,U) (KaehlerDifferential k K) :=
    Module.compHom (KaehlerDifferential k K) (X.germToFunctionField U).hom
  letI : IsScalarTower Γ(X,U) K (KaehlerDifferential k K) :=
    IsScalarTower.of_compHom _ _ _
  exact ((basisTopExteriorEquiv b).toLinearMap.restrictScalars Γ(X,U)).comp
    (exteriorScalarExtensionMap (R := Γ(X,U)) (S := K)
      (M := Γ(differentialSheaf k X,U)) (N := KaehlerDifferential k K) (n := n)
      (differentialSectionValue X k U))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
@[simp] theorem genericTopCoefficientValue_wedge (U : X.Opens) [Nonempty U]
    (ω : Fin n→Γ(ΩX,U)) :
    genericTopCoefficientValue X k b U (exteriorPower.ιMulti Γ(X,U) n ω)=
      basisTopExteriorEquiv b (exteriorPower.ιMulti K n
        (fun i=>differentialSectionValue X k U (ω i))) := by
  letI : Algebra Γ(X,U) K := (X.germToFunctionField U).hom.toAlgebra
  letI : Module Γ(X,U) (KaehlerDifferential k K) :=
    Module.compHom (KaehlerDifferential k K) (X.germToFunctionField U).hom
  letI : IsScalarTower Γ(X,U) K (KaehlerDifferential k K) :=
    IsScalarTower.of_compHom _ _ _
  exact congrArg (basisTopExteriorEquiv b)
    (exteriorScalarExtensionMap_wedge (R := Γ(X,U)) (S := K)
      (M := Γ(differentialSheaf k X,U)) (N := KaehlerDifferential k K) (n := n)
      (differentialSectionValue X k U) ω)

def genericTopCoefficientSection (U : X.Opens) :
    (P).obj (op U)→ₗ[Γ(X,U)]Γ(rationalFunctions X,U) :=
  if hU : Nonempty U then
    (rationalValueLinearEquiv X U).symm.toLinearMap.comp
      (genericTopCoefficientValue X k b U)
  else 0

@[simp] theorem genericTopCoefficientSection_value (U : X.Opens) [Nonempty U]
    (ω : (P).obj (op U)) :
    rationalValue X U (genericTopCoefficientSection X k b U ω)=
      genericTopCoefficientValue X k b U ω := by
  simp only [genericTopCoefficientSection,dif_pos (show Nonempty U from inferInstance),
    LinearMap.comp_apply]
  exact (rationalValueLinearEquiv X U).apply_symm_apply _

theorem genericTopCoefficientSection_natural {U V : X.Opens} (i : V⟶U) :
    (P).map i.op ≫ (ModuleCat.restrictScalars (X.presheaf.map i.op).hom).map
        (ModuleCat.ofHom (genericTopCoefficientSection X k b V)) =
      ModuleCat.ofHom (genericTopCoefficientSection X k b U) ≫
        (rationalFunctions X).val.map i.op := by
  by_cases hV : Nonempty V
  · letI := hV
    letI : Nonempty U := ⟨⟨(Classical.choice hV).val,i.le (Classical.choice hV).property⟩⟩
    apply ModuleCat.exteriorPower.hom_ext (R := Γ(X,U)) (n := n)
      (M := PresheafOfModulesOfCommRing.obj (R := X.presheaf)
        (SheafOfModules.val (differentialSheaf k X)) (op U))
      (N := (ModuleCat.restrictScalars (X.presheaf.map i.op).hom).obj
        ((rationalFunctions X).val.obj (op V)))
    apply ModuleCat.AlternatingMap.ext
    intro ω
    change genericTopCoefficientSection X k b V
        ((P).map i.op (exteriorPower.ιMulti Γ(X,U) n ω)) =
      (rationalFunctions X).presheaf.map i.op
        (genericTopCoefficientSection X k b U (exteriorPower.ιMulti Γ(X,U) n ω))
    apply (rationalValue X V).injective
    let ω' : Fin n→Γ(differentialSheaf k X,V) :=
      fun a => (differentialSheaf k X).presheaf.map i.op (ω a)
    calc
      _ = genericTopCoefficientValue X k b V
          ((P).map i.op (exteriorPower.ιMulti Γ(X,U) n ω)) :=
        genericTopCoefficientSection_value X k b V _
      _ = genericTopCoefficientValue X k b V (exteriorPower.ιMulti Γ(X,V) n ω') :=
        congrArg (genericTopCoefficientValue X k b V)
          (presheafExteriorPower_map_wedge X.presheaf
            (SheafOfModules.val (differentialSheaf k X)) n i.op ω)
      _ = basisTopExteriorEquiv b (exteriorPower.ιMulti K n
          (fun a => differentialSectionValue X k V (ω' a))) :=
        genericTopCoefficientValue_wedge X k b V ω'
      _ = basisTopExteriorEquiv b (exteriorPower.ιMulti K n
          (fun a => differentialSectionValue X k U (ω a))) :=
        congrArg (fun v => basisTopExteriorEquiv b (exteriorPower.ιMulti K n v))
          (funext (fun a => differentialSectionValue_restrict X k i (ω a)))
      _ = _ := ((rationalValue_restrict X i _).trans
        ((genericTopCoefficientSection_value X k b U _).trans
          (genericTopCoefficientValue_wedge X k b U ω))).symm
  · have hbot : V=⊥ := by
      apply le_antisymm
      · intro x hx
        exact False.elim (hV ⟨⟨x,hx⟩⟩)
      · exact bot_le
    ext ω
    exact @Subsingleton.elim Γ(rationalFunctions X,V)
      (moduleSections_subsingleton_of_empty (rationalFunctions X) V hbot) _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- The presheaf map uses ordinary generic differential coefficients on
every nonempty open and the unique zero section on the empty open. -/
def genericTopCoefficientPresheaf : P⟶(rationalFunctions X).val :=
  PresheafOfModulesOfCommRing.homMk (R := X.presheaf)
    (M₁ := P) (M₂ := (rationalFunctions X).val)
    (fun U=>ModuleCat.ofHom (R := Γ(X,U.unop))
      (X := (P).obj U) (Y := Γ(rationalFunctions X,U.unop))
      (genericTopCoefficientSection X k b U.unop))
    (fun f=>genericTopCoefficientSection_natural X k b f.unop)

/-- The actual generic-coefficient morphism from the ordinary top
exterior sheaf of the intrinsic Kähler sheaf. -/
def topDifferentialRationalMap : topDifferentialSheaf k X n⟶rationalFunctions X :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv
    P (rationalFunctions X)).symm (genericTopCoefficientPresheaf X k b)

theorem topDifferentialRationalMap_unit :
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P ≫
      (topDifferentialRationalMap X k b).val=genericTopCoefficientPresheaf X k b := by
  exact ((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).homEquiv P (rationalFunctions X)).apply_symm_apply _

def differentialWedgeSection (U : X.Opens) (a : Fin n→Γ(X,U)) :
    Γ(topDifferentialSheaf k X n,U) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P).app
    (op U) (exteriorPower.ιMulti Γ(X,U) n
      (fun i=>(differentialSheafDerivation k X).d (X:=op U) (a i)))

theorem differentialWedgeSection_restrict {U V : X.Opens} (h : V≤U)
    (a : Fin n→Γ(X,U)) :
    moduleRes (topDifferentialSheaf k X n) h (differentialWedgeSection X k U a)=
      differentialWedgeSection X k V (fun i=>regularRes h (a i)) := by
  let η : P⟶(topDifferentialSheaf k X n).val :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P
  let v := exteriorPower.ιMulti Γ(X,U) n
    (fun i=>(differentialSheafDerivation k X).d (X:=op U) (a i))
  have hv : (P).map (homOfLE h).op v = exteriorPower.ιMulti Γ(X,V) n
      (fun i=>(differentialSheafDerivation k X).d (X:=op V) (regularRes h (a i))) := by
    calc
      _ = exteriorPower.ιMulti Γ(X,V) n (M := Γ(differentialSheaf k X,V))
          (fun i=>(differentialSheaf k X).presheaf.map (homOfLE h).op
            ((differentialSheafDerivation k X).d (X:=op U) (a i))) :=
        presheafExteriorPower_map_wedge X.presheaf
          (SheafOfModules.val (differentialSheaf k X)) n (homOfLE h).op _
      _ = _ := congrArg (fun v : Fin n→Γ(differentialSheaf k X,V) =>
          exteriorPower.ιMulti Γ(X,V) n v)
        (funext (fun i =>
          ((differentialSheafDerivation k X).d_map (homOfLE h).op (a i)).symm))
  exact (PresheafOfModules.naturality_apply η (homOfLE h).op v).symm.trans
    (congrArg (η.app (op V)) hv)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
theorem differentialWedgeSection_openRestriction
    {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k))]
    (j : Y⟶X) [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k))]
    (U : Y.Opens) (a : Fin n→Γ(X,j ''ᵁ U)) :
    (topDifferentialSheafRestrictIso j n k).hom.app U
      (((topDifferentialSheaf k X n).restrictAppIso j U).inv
        (differentialWedgeSection X k (j ''ᵁ U) a)) =
      differentialWedgeSection Y k U (fun i=>(j.appIso U).hom (a i)) := by
  let P₀ := presheafExteriorPower X.presheaf (differentialSheaf k X).val n
  let P₁ := presheafExteriorPower Y.presheaf ((differentialSheaf k X).restrict j).val n
  let P₂ := presheafExteriorPower Y.presheaf (differentialSheaf k Y).val n
  let η₁ : P₁⟶(sheafExteriorPower Y ((differentialSheaf k X).restrict j) n).val :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app P₁
  let η₂ : P₂⟶(topDifferentialSheaf k Y n).val :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app P₂
  let ωX : Fin n→Γ(differentialSheaf k X,j ''ᵁ U) :=
    fun i=>(differentialSheafDerivation k X).d (X:=op (j ''ᵁ U)) (a i)
  let ωY : Fin n→Γ((differentialSheaf k X).restrict j,U) :=
    fun i=>((differentialSheaf k X).restrictAppIso j U).inv (ωX i)
  let wX := exteriorPower.ιMulti Γ(X,j ''ᵁ U) n ωX
  let wY := exteriorPower.ιMulti Γ(Y,U) n ωY
  have hW : (openPresheafExteriorIso j (differentialSheaf k X).val n).inv.app (op U) wX = wY := by
    change (ringExteriorIso (R := X.presheaf.obj (op (j ''ᵁ U)))
      (S := Y.presheaf.obj (op U)) (j.appIso U)
      (PresheafOfModulesOfCommRing.obj (R := X.presheaf)
        (differentialSheaf k X).val (op (j ''ᵁ U))) n).inv wX = wY
    exact ringExteriorIso_inv_wedge (j.appIso U)
      (PresheafOfModulesOfCommRing.obj (R := X.presheaf)
        (differentialSheaf k X).val (op (j ''ᵁ U))) n ωX
  have hu := congrArg
    (fun f : (openPresheafRestrict j).obj P₀⟶
        (sheafExteriorPower Y ((differentialSheaf k X).restrict j) n).val =>
      f.app (op U) wX)
    (sheafExteriorRestrictIso_unit j n (differentialSheaf k X))
  change (sheafExteriorRestrictIso j n (differentialSheaf k X)).hom.app U
      (((topDifferentialSheaf k X n).restrictAppIso j U).inv
        (differentialWedgeSection X k (j ''ᵁ U) a)) =
    η₁.app (op U) ((openPresheafExteriorIso j (differentialSheaf k X).val n).inv.app (op U) wX) at hu
  have hu' := hu.trans (congrArg (η₁.app (op U)) hW)
  let m : P₁⟶P₂ :=
    presheafExteriorPowerHom Y.presheaf n (differentialSheafRestrictIso k j).hom.val
  have hn := (PresheafOfModules.sheafificationAdjunction
    (𝟙 Y.ringCatSheaf.obj)).unit.naturality m
  have hn' : η₂.app (op U) (m.app (op U) wY) =
      (sheafExteriorPowerIso Y (differentialSheafRestrictIso k j) n).hom.app U
        (η₁.app (op U) wY) :=
    congrArg (fun f : P₁⟶(topDifferentialSheaf k Y n).val => f.app (op U) wY) hn
  have hMap : m.app (op U) wY = exteriorPower.ιMulti Γ(Y,U) n
      (fun i=>(differentialSheafDerivation k Y).d (X:=op U) ((j.appIso U).hom (a i))) := by
    change ModuleCat.exteriorPower.map (R := Γ(Y,U))
      ((differentialSheafRestrictIso k j).hom.val.app (op U)) n wY = _
    exact (ModuleCat.exteriorPower.map_mk (R := Γ(Y,U))
      ((differentialSheafRestrictIso k j).hom.val.app (op U)) ωY).trans
        (congrArg (fun v : Fin n→Γ(differentialSheaf k Y,U) =>
          exteriorPower.ιMulti Γ(Y,U) n v)
          (funext (fun i=>differentialSheafRestrictIso_D k j U (a i))))
  change (sheafExteriorPowerIso Y (differentialSheafRestrictIso k j) n).hom.app U
    ((sheafExteriorRestrictIso j n (differentialSheaf k X)).hom.app U
      (((topDifferentialSheaf k X n).restrictAppIso j U).inv
        (differentialWedgeSection X k (j ''ᵁ U) a)))=_
  exact (congrArg ((sheafExteriorPowerIso Y (differentialSheafRestrictIso k j) n).hom.app U)
    hu').trans (hn'.symm.trans (congrArg (η₂.app (op U)) hMap))

/-- On a wedge of genuine differentials of regular functions the map
is exactly the wedge of their generic differentials. -/
theorem topDifferentialRationalMap_differentialWedge
    (U : X.Opens) [Nonempty U] (a : Fin n→Γ(X,U)) :
    rationalValue X U ((topDifferentialRationalMap X k b).app U
      (differentialWedgeSection X k U a))=
        basisTopExteriorEquiv b (exteriorPower.ιMulti K n
          (fun i=>KaehlerDifferential.D k K (X.germToFunctionField U (a i)))) := by
  have h := congrArg
    (fun f=>f.app (op U) (exteriorPower.ιMulti Γ(X,U) n
      (fun i=>(differentialSheafDerivation k X).d (X:=op U) (a i))))
    (topDifferentialRationalMap_unit X k b)
  change (topDifferentialRationalMap X k b).app U
    (differentialWedgeSection X k U a)=
      genericTopCoefficientSection X k b U
        (exteriorPower.ιMulti Γ(X,U) n
          (fun i=>(differentialSheafDerivation k X).d (X:=op U) (a i))) at h
  exact (congrArg (rationalValue X U) h).trans
    ((genericTopCoefficientSection_value X k b U _).trans
      ((genericTopCoefficientValue_wedge X k b U _).trans
        (congrArg (fun v : Fin n → KaehlerDifferential k K =>
          basisTopExteriorEquiv b (exteriorPower.ιMulti K n v))
            (funext (fun i => differentialSectionValue_D X k U (a i))))))

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.topDifferentialRationalMap_differentialWedge

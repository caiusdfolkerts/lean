module

public import Lean.Elab.BuiltinEvalCommand
public meta import Lean.Elab.BuiltinEvalCommand
public import Lean.Util.CollectAxioms
public meta import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public meta import Lean.Util.FoldConsts
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import paper_verification.toric010
public import paper_verification.toric023
public import paper_verification.toric033
public import paper_verification.toric034
public import paper_verification.toric035
public import paper_verification.toric036

@[expose] public section


-- BEGIN ORIGINAL PaperVerification.ToricGenericDifferentialSections
section Source_ToricGenericDifferentialSections

-- original header: module

-- original header: public import PaperVerification.ToricIntrinsicDifferentialSheaf
-- original header: public import PaperVerification.ToricRationalSheaf
-- original header: public import PaperVerification.ToricModuleFrameGluing
-- original header: public import Mathlib.AlgebraicGeometry.Modules.Tilde

-- original header: @[expose] public section

/-!
# Actual values of differential sections at the generic point

For any module over the actual function field, its tilde sheaf on the
generic-point scheme is pushed forward to the original integral scheme.
Its sections on every nonempty open are identified with the original
module. The universal differential of regular functions then gives an
actual morphism from the intrinsic Kähler sheaf into this generic module.
All restriction and scalar compatibilities are proved from actual sheaf
maps, and d(r) has value d(germ(r)).
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped BaseSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

variable (X : Scheme.{u}) [IsIntegral X]
    (N : ModuleCat.{u} X.functionField)

/-- A genuine module sheaf supported at the actual generic point. -/
def genericModule : X.Modules :=
  (Scheme.Modules.pushforward (genericPointMap X)).obj (tilde N)

def genericModuleValueAdd (U : X.Opens) [Nonempty U] :
    Γ(genericModule X N,U)≃+N :=
  ((tilde N).presheaf.mapIso
    (eqToIso (congrArg op (genericPointMap_preimage X U)))).addCommGroupIsoToAddEquiv.trans
      (tilde.isoTop N).toLinearEquiv.toAddEquiv.symm

theorem genericModuleValueAdd_restrict {U V : X.Opens}
    [Nonempty U] [Nonempty V] (i : V⟶U) (s : Γ(genericModule X N,U)) :
    genericModuleValueAdd X N V ((genericModule X N).presheaf.map i.op s)=
      genericModuleValueAdd X N U s := by
  change (tilde.isoTop N).inv
      ((tilde N).presheaf.map
        (eqToHom (congrArg op (genericPointMap_preimage X V)))
          ((tilde N).presheaf.map
            ((Opens.map (genericPointMap X).base).map i).op s))=
    (tilde.isoTop N).inv
      ((tilde N).presheaf.map
        (eqToHom (congrArg op (genericPointMap_preimage X U))) s)
  congr 1

set_option backward.isDefEq.respectTransparency.types false in
theorem genericModuleValueAdd_smul (U : X.Opens) [Nonempty U]
    (a : Γ(X,U)) (s : Γ(genericModule X N,U)) :
    genericModuleValueAdd X N U (a • s)=
      X.germToFunctionField U a • genericModuleValueAdd X N U s := by
  let φ := eqToHom (congrArg op (genericPointMap_preimage X U))
  let t := (tilde N).presheaf.map φ s
  have hscalar : (Spec X.functionField).presheaf.map φ ((genericPointMap X).app U a)=
      (Scheme.ΓSpecIso X.functionField).inv (X.germToFunctionField U a) := by
    have h := congrArg (fun f=>f a) (genericPointMap_app_value X U)
    change (Scheme.ΓSpecIso X.functionField).hom
      ((Spec X.functionField).presheaf.map φ ((genericPointMap X).app U a)) =
        X.germToFunctionField U a at h
    simpa only [Iso.hom_inv_id_apply] using
      congrArg (fun t => (Scheme.ΓSpecIso X.functionField).inv t) h
  change (tilde.isoTop N).inv
      ((tilde N).val.map φ ((genericPointMap X).app U a •
        (show Γ(tilde N,genericPointMap X ⁻¹ᵁ U) from s)))=
    X.germToFunctionField U a • (tilde.isoTop N).inv t
  rw [(tilde N).val.map_smul]
  erw [hscalar]
  change (tilde.isoTop N).inv ((X.germToFunctionField U a) • t)=_
  exact (tilde.isoTop N).inv.hom.map_smul _ _

/-- The scalar action on N is restriction through the actual germ map. -/
def genericModuleValue (U : X.Opens) [Nonempty U] :
    Γ(genericModule X N,U)≃ₗ[Γ(X,U)]
      (ModuleCat.restrictScalars (X.germToFunctionField U).hom).obj N where
  __ := genericModuleValueAdd X N U
  map_smul' a s := genericModuleValueAdd_smul X N U a s

@[simp] theorem genericModuleValue_restrict {U V : X.Opens}
    [Nonempty U] [Nonempty V] (i : V⟶U) (s : Γ(genericModule X N,U)) :
    genericModuleValue X N V ((genericModule X N).presheaf.map i.op s)=
      genericModuleValue X N U s :=
  genericModuleValueAdd_restrict X N i s

section Differentials

variable (k : Type u) [CommRing k] [X.Over (Spec (CommRingCat.of k))]

local notation "ΩK" => ModuleCat.of X.functionField (KaehlerDifferential k X.functionField)
local notation "GΩ" => genericModule X ΩK

def genericDifferentialDerivationValue (U : X.Opens) : Γ(X,U)→+Γ(GΩ,U) := by
  classical
  exact if hU : Nonempty U then
    (genericModuleValue X ΩK U).symm.toAddEquiv.toAddMonoidHom.comp
      ((KaehlerDifferential.D k X.functionField).toLinearMap.toAddMonoidHom.comp
        (X.germToFunctionField U).hom.toAddMonoidHom)
  else 0

theorem genericDifferentialDerivationValue_value (U : X.Opens) [Nonempty U]
    (a : Γ(X,U)) :
    genericModuleValue X ΩK U (genericDifferentialDerivationValue X k U a)=
      KaehlerDifferential.D k X.functionField (X.germToFunctionField U a) := by
  simp only [genericDifferentialDerivationValue,dif_pos (show Nonempty U from inferInstance),
    AddMonoidHom.comp_apply,LinearEquiv.apply_symm_apply]
  exact (genericModuleValue X ΩK U).apply_symm_apply _

theorem genericDifferentialDerivationValue_mul (U : X.Opens) (a b : Γ(X,U)) :
    genericDifferentialDerivationValue X k U (a*b)=
      a • genericDifferentialDerivationValue X k U b+
        b • genericDifferentialDerivationValue X k U a := by
  classical
  by_cases hU : Nonempty U
  · letI := hU
    apply (genericModuleValue X ΩK U).injective
    simp only [genericDifferentialDerivationValue_value,map_add,map_smul,map_mul]
    exact (KaehlerDifferential.D k X.functionField).leibniz
      (X.germToFunctionField U a) (X.germToFunctionField U b)
  · have hbot : U=⊥ := by
      apply le_antisymm
      · intro x hx
        exact False.elim (hU ⟨⟨x,hx⟩⟩)
      · exact bot_le
    letI := moduleSections_subsingleton_of_empty GΩ U hbot
    exact Subsingleton.elim _ _

theorem genericDifferentialDerivationValue_restrict {U V : X.Opens}
    (i : V⟶U) (a : Γ(X,U)) :
    genericDifferentialDerivationValue X k V (X.presheaf.map i.op a)=
      (GΩ).presheaf.map i.op (genericDifferentialDerivationValue X k U a) := by
  classical
  by_cases hV : Nonempty V
  · letI := hV
    letI : Nonempty U := ⟨⟨(Classical.choice hV).val,i.le (Classical.choice hV).property⟩⟩
    apply (genericModuleValue X ΩK V).injective
    rw [genericDifferentialDerivationValue_value,genericModuleValue_restrict,
      genericDifferentialDerivationValue_value,germToFunctionField_restrict]
  · have hbot : V=⊥ := by
      apply le_antisymm
      · intro x hx
        exact False.elim (hV ⟨⟨x,hx⟩⟩)
      · exact bot_le
    letI := moduleSections_subsingleton_of_empty GΩ V hbot
    exact Subsingleton.elim _ _

theorem genericDifferentialDerivationValue_scalar (U : X.Opens) (a : k) :
    genericDifferentialDerivationValue X k U (BaseSections.scalarMap k X U a)=0 := by
  classical
  by_cases hU : Nonempty U
  · letI := hU
    apply (genericModuleValue X ΩK U).injective
    rw [genericDifferentialDerivationValue_value,map_zero,BaseSections.germ_scalarMap]
    exact (KaehlerDifferential.D k X.functionField).map_algebraMap a
  · simp only [genericDifferentialDerivationValue,dif_neg hU,AddMonoidHom.zero_apply]

/-- The ordinary universal differential of actual regular functions,
with values in the genuine pushed-forward generic module. -/
def genericDifferentialDerivation :
    PresheafOfModulesOfCommRing.Derivation' (R := X.presheaf)
      (GΩ).val (scalarPresheafMap k X) where
  d {U} := genericDifferentialDerivationValue X k U.unop
  d_mul {U} := genericDifferentialDerivationValue_mul X k U.unop
  d_map {U V} f a := genericDifferentialDerivationValue_restrict X k f.unop a
  d_app {U} := genericDifferentialDerivationValue_scalar X k U.unop

/-- The genuine sheaf morphism supplied by the universal Kähler
derivation and the actual module-sheafification adjunction. -/
def differentialGenericMap : differentialSheaf k X⟶GΩ :=
  (differentialSheafHomEquiv k X GΩ).symm (genericDifferentialDerivation X k)

/-- Differential sections have actual generic values linear over the
regular-function ring through the actual germ map. -/
def differentialSectionValue (U : X.Opens) [Nonempty U] :
    Γ(differentialSheaf k X,U)→ₗ[Γ(X,U)]
      (ModuleCat.restrictScalars (X.germToFunctionField U).hom).obj ΩK :=
  (genericModuleValue X ΩK U).toLinearMap.comp
    ((differentialGenericMap X k).val.app (op U)).hom

set_option backward.isDefEq.respectTransparency.types false in
theorem differentialSectionValue_restrict {U V : X.Opens}
    [Nonempty U] [Nonempty V] (i : V⟶U)
    (s : Γ(differentialSheaf k X,U)) :
    differentialSectionValue X k V ((differentialSheaf k X).presheaf.map i.op s)=
      differentialSectionValue X k U s := by
  change genericModuleValue X ΩK V
      ((differentialGenericMap X k).app V
        ((differentialSheaf k X).presheaf.map i.op s)) =
    genericModuleValue X ΩK U ((differentialGenericMap X k).app U s)
  have hn := congrArg (fun f => f s)
    ((Scheme.Modules.Hom.mapPresheaf (differentialGenericMap X k)).naturality i.op)
  exact (congrArg (genericModuleValue X ΩK V) hn).trans
    (genericModuleValue_restrict X ΩK i ((differentialGenericMap X k).app U s))

theorem differentialGenericMap_D (U : X.Opens) (a : Γ(X,U)) :
    (differentialGenericMap X k).app U
      ((differentialSheafDerivation k X).d (X:=op U) a)=
        genericDifferentialDerivationValue X k U a := by
  have h := (differentialSheafHomEquiv k X GΩ).apply_symm_apply
    (genericDifferentialDerivation X k)
  rw [differentialSheafHomEquiv_apply] at h
  exact PresheafOfModulesOfCommRing.Derivation.congr_d h a

set_option backward.isDefEq.respectTransparency.types false in
/-- The value of d(a) is precisely the ordinary algebraic differential
of the actual generic germ of a. -/
theorem differentialSectionValue_D (U : X.Opens) [Nonempty U] (a : Γ(X,U)) :
    differentialSectionValue X k U ((differentialSheafDerivation k X).d (X:=op U) a)=
      KaehlerDifferential.D k X.functionField (X.germToFunctionField U a) := by
  change genericModuleValue X ΩK U
    ((differentialGenericMap X k).app U
      ((differentialSheafDerivation k X).d (X:=op U) a)) = _
  exact (congrArg (genericModuleValue X ΩK U)
    (differentialGenericMap_D X k U a)).trans
      (genericDifferentialDerivationValue_value X k U a)

end Differentials

end PaperVerification.ToricSchemes
end
end Source_ToricGenericDifferentialSections
-- END ORIGINAL PaperVerification.ToricGenericDifferentialSections


-- BEGIN ORIGINAL PaperVerification.ToricGenericTopDifferentials
section Source_ToricGenericTopDifferentials

-- original header: module

-- original header: public import PaperVerification.ToricGenericDifferentialSections
-- original header: public import PaperVerification.ToricExteriorRestriction

-- original header: @[expose] public section

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
end
end Source_ToricGenericTopDifferentials
-- END ORIGINAL PaperVerification.ToricGenericTopDifferentials


-- BEGIN ORIGINAL PaperVerification.ToricAffineDifferentialWedges
section Source_ToricAffineDifferentialWedges

-- original header: module

-- original header: public import PaperVerification.ToricAffineExteriorSheaf
-- original header: public import PaperVerification.ToricGenericTopDifferentials

-- original header: @[expose] public section

/-! # The affine comparison preserves actual wedges of differentials -/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite
open scoped BaseSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

variable {X : Scheme.{u}} {M N : X.Modules} (e : M≅N) (n : ℕ)

theorem sheafExteriorPowerIso_wedge (U : X.Opens) (ω : Fin n→Γ(M,U)) :
    (sheafExteriorPowerIso X e n).hom.app U
      (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        (presheafExteriorPower X.presheaf M.val n)).app (op U)
          (exteriorPower.ιMulti Γ(X,U) n ω)) =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        (presheafExteriorPower X.presheaf N.val n)).app (op U)
          (exteriorPower.ιMulti Γ(X,U) n (fun i=>e.hom.app U (ω i))) := by
  have h := congrArg
    (fun f=>f.app (op U) (exteriorPower.ιMulti Γ(X,U) n ω))
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.naturality
      (presheafExteriorPowerHom X.presheaf n e.hom.val))
  change
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      (presheafExteriorPower X.presheaf N.val n)).app (op U)
        (ModuleCat.exteriorPower.map (R := Γ(X,U)) (e.hom.val.app (op U)) n
          (exteriorPower.ιMulti Γ(X,U) n ω)) =
      (sheafExteriorPowerIso X e n).hom.app U
        (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (presheafExteriorPower X.presheaf M.val n)).app (op U)
            (exteriorPower.ιMulti Γ(X,U) n ω)) at h
  have hmap :
      ModuleCat.exteriorPower.map (R := Γ(X,U)) (e.hom.val.app (op U)) n
        (exteriorPower.ιMulti Γ(X,U) n ω) =
      exteriorPower.ιMulti Γ(X,U) n (fun i=>e.hom.app U (ω i)) :=
    ModuleCat.exteriorPower.map_mk (R := Γ(X,U)) (e.hom.val.app (op U)) ω
  exact h.symm.trans (congrArg
    (fun x=>((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      (presheafExteriorPower X.presheaf N.val n)).app (op U) x) hmap)

variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R] {n : ℕ}
    (b : Module.Basis (Fin n) R (KaehlerDifferential k R))

local instance affineWedgeCoordinateAlgebra (U : (Spec (CommRingCat.of R)).Opens) :
    Algebra R Γ(Spec (CommRingCat.of R),U) :=
  inferInstanceAs (Algebra R
    ((Spec.structureSheaf (CommRingCat.of R)).presheaf.obj (op U)))

theorem affineTopDifferentialSheafIso_differentialWedge (f : R) (a : Fin n→R) :
    (affineTopDifferentialSheafIso k R b).hom.app (PrimeSpectrum.basicOpen f)
      (differentialWedgeSection (Spec (CommRingCat.of R)) k
        (PrimeSpectrum.basicOpen f)
        (fun i=>algebraMap R Γ(Spec (CommRingCat.of R),PrimeSpectrum.basicOpen f) (a i))) =
      tilde.toOpen (R := CommRingCat.of R) (ModuleCat.of R (⋀[R]^n (KaehlerDifferential k R)))
        (PrimeSpectrum.basicOpen f)
          (exteriorPower.ιMulti R n (fun i=>KaehlerDifferential.D k R (a i))) := by
  let U : (Spec (CommRingCat.of R)).Opens := PrimeSpectrum.basicOpen f
  let ω : Fin n→Γ(differentialSheaf k (Spec (CommRingCat.of R)),U) :=
    fun i=>(differentialSheafDerivation k (Spec (CommRingCat.of R))).d
      («X» := op U) (algebraMap R Γ(Spec (CommRingCat.of R),U) (a i))
  have hw := sheafExteriorPowerIso_wedge (affineDifferentialSheafIso k R) n U ω
  have hv : (fun i=>(affineDifferentialSheafIso k R).hom.app U (ω i)) =
      (fun i=>tilde.toOpen (R := CommRingCat.of R)
        (ModuleCat.of R (KaehlerDifferential k R)) U
          (KaehlerDifferential.D k R (a i))) := by
    funext i
    exact affineDifferentialSheafIso_D k R f (a i)
  have hη := congrArg
    (fun v=>((PresheafOfModules.sheafificationAdjunction
      (𝟙 (Spec (CommRingCat.of R)).ringCatSheaf.obj)).unit.app
        (presheafExteriorPower (Spec (CommRingCat.of R)).presheaf
          (tilde (R := CommRingCat.of R) (ModuleCat.of R (KaehlerDifferential k R))).val n)).app
            (op U) (exteriorPower.ιMulti Γ(Spec (CommRingCat.of R),U) n v)) hv
  exact (congrArg
    (fun z=>(affineTopExteriorSheafIso (CommRingCat.of R)
      (ModuleCat.of R (KaehlerDifferential k R)) b).hom.app U z)
      (hw.trans hη)).trans
    (affineTopExteriorSheafIso_wedge (CommRingCat.of R)
      (ModuleCat.of R (KaehlerDifferential k R)) b f
        (fun i=>KaehlerDifferential.D k R (a i)))

theorem affineTopDifferentialSheafIso_differentialWedge_top (a : Fin n→R) :
    (affineTopDifferentialSheafIso k R b).hom.app ⊤
      (differentialWedgeSection (Spec (CommRingCat.of R)) k ⊤
        (fun i=>(Scheme.ΓSpecIso (CommRingCat.of R)).inv (a i))) =
      tilde.toOpen (R := CommRingCat.of R) (ModuleCat.of R (⋀[R]^n (KaehlerDifferential k R))) ⊤
        (exteriorPower.ιMulti R n (fun i=>KaehlerDifferential.D k R (a i))) := by
  have h := affineTopDifferentialSheafIso_differentialWedge k R b 1 a
  have hU : (PrimeSpectrum.basicOpen (1 : R) : (Spec (CommRingCat.of R)).Opens)=⊤ :=
    PrimeSpectrum.basicOpen_one
  erw [hU] at h
  have htop (r : R) : algebraMap R Γ(Spec (CommRingCat.of R),⊤) r =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv r := by
    change (Spec (CommRingCat.of R)).presheaf.map (𝟙 (op ⊤))
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) = _
    exact congrArg (fun φ=>φ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))
      ((Spec (CommRingCat.of R)).presheaf.map_id (op ⊤))
  simpa only [htop] using h

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.affineTopDifferentialSheafIso_differentialWedge_top
end
end Source_ToricAffineDifferentialWedges
-- END ORIGINAL PaperVerification.ToricAffineDifferentialWedges


-- BEGIN ORIGINAL PaperVerification.ToricFanDifferentials
section Source_ToricFanDifferentials

-- original header: module

-- original header: public import PaperVerification.ToricFractionDifferentials
-- original header: public import PaperVerification.ToricFanCartierCocycle
-- original header: public import PaperVerification.ToricFanSectionCoordinates

-- original header: @[expose] public section

/-!
# Actual generic and affine-chart differential forms on the fan scheme

The coefficient field is the actual generic stalk of the glued scheme.
Its algebra structures are explicitly induced by the previously proved
chart maps. The fraction-field assertion is transferred from the actual
open affine zero-cone chart. Full-chart Kähler bases are then constructed
through the literal polynomial character presentations.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory AddMonoidAlgebra KaehlerDifferential
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped BigOperators Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

def fanFunctionFieldAlgebra : Algebra k («Σ».fanScheme k).functionField :=
  BaseSections.functionFieldAlgebra k («Σ».fanScheme k)

def torusFunctionFieldAlgebra :
    Algebra (AddMonoidAlgebra k (Lattice n)) («Σ».fanScheme k).functionField :=
  («Σ».torusRationalMap k).toAlgebra

def chartFunctionFieldAlgebra (s : «Σ».ConeIndex) :
    Algebra (monoidChartAlgebra k (dualConeMonoid s.val)) («Σ».fanScheme k).functionField :=
  («Σ».chartRationalMap k s).toAlgebra

attribute [local instance] fanFunctionFieldAlgebra torusFunctionFieldAlgebra
  chartFunctionFieldAlgebra

instance fanFunctionField_scalarTower :
    IsScalarTower k (AddMonoidAlgebra k (Lattice n)) («Σ».fanScheme k).functionField :=
  IsScalarTower.of_algebraMap_eq fun r => («Σ».rationalScalar_eq_algebraMap k r).symm

instance chartFunctionField_scalarTower (s : «Σ».ConeIndex) :
    IsScalarTower k (monoidChartAlgebra k (dualConeMonoid s.val))
      («Σ».fanScheme k).functionField :=
  ⟨fun r a z => smul_assoc r (a : AddMonoidAlgebra k (Lattice n)) z⟩

instance chartTorusFunctionField_scalarTower (s : «Σ».ConeIndex) :
    IsScalarTower (monoidChartAlgebra k (dualConeMonoid s.val))
      (AddMonoidAlgebra k (Lattice n)) («Σ».fanScheme k).functionField :=
  ⟨fun a r z => smul_assoc (a : AddMonoidAlgebra k (Lattice n)) r z⟩

/-- This localization is for the exact character map into the generic
stalk, not for an independently chosen isomorphic field. -/
theorem torusFunctionField_isFractionRing :
    IsFractionRing (AddMonoidAlgebra k (Lattice n)) («Σ».fanScheme k).functionField := by
  let R := monoidChartAlgebra k (dualConeMonoid (∅ : Finset (Lattice n)))
  letI : IsDomain R := «Σ».chartRing_isDomain k ∅ «Σ».zeroConeIndex.property
  let j : Spec (CommRingCat.of R) ⟶ «Σ».fanScheme k := «Σ».torusOpenMap k
  letI : IsOpenImmersion j := «Σ».torusOpenMap_isOpenImmersion k
  letI : Algebra R («Σ».fanScheme k).functionField :=
    affineOpenCoordinateAlgebra (CommRingCat.of R) j
  letI : IsFractionRing R («Σ».fanScheme k).functionField :=
    affineOpenCoordinate_isFractionRing (CommRingCat.of R) j
  exact IsFractionRing.of_ringEquiv_left (zeroConeChartAlgEquiv k n).symm.toRingEquiv
    (fun _ => rfl)

attribute [local instance] torusFunctionField_isFractionRing

def genericLogDifferentialBasis (b : Module.Basis (Fin n) ℤ (Lattice n)) :
    Module.Basis (Fin n) («Σ».fanScheme k).functionField
      Ω[(«Σ».fanScheme k).functionField⁄k] :=
  fractionLogDifferentialBasis k («Σ».fanScheme k).functionField b

def genericLogVolume (b : Module.Basis (Fin n) ℤ (Lattice n)) :
    ⋀[(«Σ».fanScheme k).functionField]^n Ω[(«Σ».fanScheme k).functionField⁄k] :=
  fractionLogVolume k («Σ».fanScheme k).functionField b

def fullCharacterBasis (s : «Σ».fullCones) : Module.Basis (Fin n) ℤ (Lattice n) :=
  integralDualBasis («Σ».fullConeBasis s)

theorem fullChart_semigroup_eq (s : «Σ».fullCones) :
    dualConeMonoid s.val = coordinateConeMonoid («Σ».fullCharacterBasis s) Finset.univ := by
  rw [«Σ».fullConeBasis_ray_set s, dualConeMonoid_basis_eq]
  rfl

def fullChartCoordinate (s : «Σ».fullCones) (i : Fin n) :
    monoidChartAlgebra k (dualConeMonoid s.val) :=
  chartCharacter k _ («Σ».fullCharacterBasis s i) (by
    rw [«Σ».fullChart_semigroup_eq]
    exact basis_mem_fullCoordinateCone _ i)

def fullChartPolynomialPresentation (s : «Σ».fullCones) :
    MvPolynomial (Fin n) k ≃ₐ[k] monoidChartAlgebra k (dualConeMonoid s.val) :=
  (fullChartPolynomialEquiv k («Σ».fullCharacterBasis s)).symm.trans
    (Subalgebra.equivOfEq _ _
      (congrArg (monoidChartAlgebra k) («Σ».fullChart_semigroup_eq s)).symm)

@[simp] theorem fullChartPolynomialPresentation_X (s : «Σ».fullCones) (i : Fin n) :
    «Σ».fullChartPolynomialPresentation k s (MvPolynomial.X i) =
      «Σ».fullChartCoordinate k s i := by
  apply Subtype.ext
  rw [fullChartPolynomialPresentation, AlgEquiv.trans_apply,
    fullChartPolynomialEquiv_symm_X]
  rfl

/-- The actual module Ω of the actual affine coordinate ring. -/
def actualFullChartDifferentialBasis (s : «Σ».fullCones) :
    Module.Basis (Fin n) (monoidChartAlgebra k (dualConeMonoid s.val))
      Ω[monoidChartAlgebra k (dualConeMonoid s.val)⁄k] :=
  polynomialDifferentialBasis k («Σ».fullChartPolynomialPresentation k s)

@[simp] theorem actualFullChartDifferentialBasis_apply (s : «Σ».fullCones) (i : Fin n) :
    «Σ».actualFullChartDifferentialBasis k s i =
      D k (monoidChartAlgebra k (dualConeMonoid s.val)) («Σ».fullChartCoordinate k s i) := by
  rw [actualFullChartDifferentialBasis, polynomialDifferentialBasis_apply,
    fullChartPolynomialPresentation_X]

@[simp] theorem map_actualFullChartDifferentialBasis (s : «Σ».fullCones) (i : Fin n) :
    KaehlerDifferential.map k k (monoidChartAlgebra k (dualConeMonoid s.val))
        («Σ».fanScheme k).functionField («Σ».actualFullChartDifferentialBasis k s i) =
      D k («Σ».fanScheme k).functionField
        («Σ».rationalCharacter k («Σ».fullCharacterBasis s i)) := by
  rw [actualFullChartDifferentialBasis_apply, KaehlerDifferential.map_D]
  congr 1

/-- Coefficients of actual chart top forms in an actual generic logarithmic
volume. This definition uses only Kähler functoriality and the universal
exterior map; the support-coefficient formula is proved afterward. -/
def actualChartTopCoefficient (b₀ : Module.Basis (Fin n) ℤ (Lattice n))
    (s : «Σ».fullCones) :
    (⋀[monoidChartAlgebra k (dualConeMonoid s.val)]^n
      Ω[monoidChartAlgebra k (dualConeMonoid s.val)⁄k]) →ₗ[
        monoidChartAlgebra k (dualConeMonoid s.val)] («Σ».fanScheme k).functionField :=
  ((basisTopExteriorEquiv («Σ».genericLogDifferentialBasis k b₀)).toLinearMap.restrictScalars _).comp
    (exteriorScalarExtensionMap (S := («Σ».fanScheme k).functionField)
      (KaehlerDifferential.map k k (monoidChartAlgebra k (dualConeMonoid s.val))
        («Σ».fanScheme k).functionField))

def chartVolumeCoefficient (b₀ : Module.Basis (Fin n) ℤ (Lattice n))
    (s : «Σ».fullCones) : ((«Σ».fanScheme k).functionField)ˣ :=
  «Σ».rationalCharacter k (∑ i, «Σ».fullCharacterBasis s i) *
    Units.map (Int.castRingHom («Σ».fanScheme k).functionField).toMonoidHom
      (b₀.isUnit_det («Σ».fullCharacterBasis s)).unit

@[simp] theorem chartVolumeCoefficient_value
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) (s : «Σ».fullCones) :
    («Σ».chartVolumeCoefficient k b₀ s : («Σ».fanScheme k).functionField) =
      («Σ».rationalCharacter k (∑ i, «Σ».fullCharacterBasis s i) : («Σ».fanScheme k).functionField) *
        (b₀.det («Σ».fullCharacterBasis s) : («Σ».fanScheme k).functionField) := rfl

theorem actualChartTopCoefficient_basis
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) (s : «Σ».fullCones) :
    «Σ».actualChartTopCoefficient k b₀ s
        (exteriorPower.ιMulti (monoidChartAlgebra k (dualConeMonoid s.val)) n
          («Σ».actualFullChartDifferentialBasis k s)) =
      («Σ».chartVolumeCoefficient k b₀ s : («Σ».fanScheme k).functionField) := by
  rw [actualChartTopCoefficient, LinearMap.comp_apply,
    exteriorScalarExtensionMap_wedge]
  simp_rw [«Σ».map_actualFullChartDifferentialBasis k s]
  change basisTopExteriorEquiv
      (fractionLogDifferentialBasis k («Σ».fanScheme k).functionField b₀)
        (fractionRegularCoordinateVolume k («Σ».fanScheme k).functionField
          («Σ».fullCharacterBasis s)) = _
  rw [fractionRegularCoordinateVolume_eq_character, map_smul,
    fractionLogVolume_change_basis k («Σ».fanScheme k).functionField b₀
      («Σ».fullCharacterBasis s), map_smul]
  change _ * ((b₀.det («Σ».fullCharacterBasis s) : («Σ».fanScheme k).functionField) *
    basisTopExteriorEquiv
      (fractionLogDifferentialBasis k («Σ».fanScheme k).functionField b₀)
      (exteriorPower.ιMulti («Σ».fanScheme k).functionField n
        (fractionLogDifferentialBasis k («Σ».fanScheme k).functionField b₀))) = _
  rw [basisTopExteriorEquiv_basis, mul_one]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual scalar action inherited from the Laurent ring agrees with
regular evaluation through the actual full-chart map. -/
theorem fullChart_functionField_smul (s : «Σ».fullCones)
    (a : monoidChartAlgebra k (dualConeMonoid s.val))
    (z : («Σ».fanScheme k).functionField) :
    a • z = «Σ».chartRationalMap k («Σ».fullConeIndex s) a * z := by
  change «Σ».torusRationalMap k (a : AddMonoidAlgebra k (Lattice n)) * z = _
  exact congrArg (fun r => r * z)
    («Σ».chartRationalMap_eq_torusRationalMap k («Σ».fullConeIndex s) a).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- Linearity and the genuine exterior basis determine every coefficient;
the scalar compatibility is proved through the actual chart morphism. -/
theorem actualChartTopCoefficient_apply
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) (s : «Σ».fullCones)
    (ω : ⋀[monoidChartAlgebra k (dualConeMonoid s.val)]^n
      Ω[monoidChartAlgebra k (dualConeMonoid s.val)⁄k]) :
    «Σ».actualChartTopCoefficient k b₀ s ω =
      «Σ».chartRationalMap k («Σ».fullConeIndex s)
        (basisTopExteriorEquiv («Σ».actualFullChartDifferentialBasis k s) ω) *
          «Σ».chartVolumeCoefficient k b₀ s := by
  calc
    _ = «Σ».actualChartTopCoefficient k b₀ s
        (basisTopExteriorEquiv («Σ».actualFullChartDifferentialBasis k s) ω •
          exteriorPower.ιMulti (monoidChartAlgebra k (dualConeMonoid s.val)) n
            («Σ».actualFullChartDifferentialBasis k s)) :=
      congrArg («Σ».actualChartTopCoefficient k b₀ s)
        (topExterior_eq_smul_basis («Σ».actualFullChartDifferentialBasis k s) ω)
    _ = basisTopExteriorEquiv («Σ».actualFullChartDifferentialBasis k s) ω •
        «Σ».actualChartTopCoefficient k b₀ s
          (exteriorPower.ιMulti (monoidChartAlgebra k (dualConeMonoid s.val)) n
            («Σ».actualFullChartDifferentialBasis k s)) := map_smul _ _ _
    _ = basisTopExteriorEquiv («Σ».actualFullChartDifferentialBasis k s) ω •
        («Σ».chartVolumeCoefficient k b₀ s : («Σ».fanScheme k).functionField) :=
      congrArg (fun z : («Σ».fanScheme k).functionField =>
        basisTopExteriorEquiv («Σ».actualFullChartDifferentialBasis k s) ω • z)
        («Σ».actualChartTopCoefficient_basis k b₀ s)
    _ = _ := «Σ».fullChart_functionField_smul k s _ _

set_option backward.isDefEq.respectTransparency.types false in
theorem mem_range_actualChartTopCoefficient_iff
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) (s : «Σ».fullCones)
    (z : («Σ».fanScheme k).functionField) :
    z ∈ LinearMap.range («Σ».actualChartTopCoefficient k b₀ s) ↔
      ∃ r : monoidChartAlgebra k (dualConeMonoid s.val),
        «Σ».chartRationalMap k («Σ».fullConeIndex s) r * «Σ».chartVolumeCoefficient k b₀ s = z := by
  constructor
  · rintro ⟨ω, rfl⟩
    exact ⟨basisTopExteriorEquiv («Σ».actualFullChartDifferentialBasis k s) ω,
      («Σ».actualChartTopCoefficient_apply k b₀ s ω).symm⟩
  · rintro ⟨r, hr⟩
    refine ⟨r • exteriorPower.ιMulti (monoidChartAlgebra k (dualConeMonoid s.val)) n
      («Σ».actualFullChartDifferentialBasis k s), ?_⟩
    calc
      _ = r • «Σ».actualChartTopCoefficient k b₀ s
          (exteriorPower.ιMulti (monoidChartAlgebra k (dualConeMonoid s.val)) n
            («Σ».actualFullChartDifferentialBasis k s)) := map_smul _ _ _
      _ = r • («Σ».chartVolumeCoefficient k b₀ s : («Σ».fanScheme k).functionField) :=
        congrArg (fun z : («Σ».fanScheme k).functionField => r • z)
          («Σ».actualChartTopCoefficient_basis k b₀ s)
      _ = «Σ».chartRationalMap k («Σ».fullConeIndex s) r *
          «Σ».chartVolumeCoefficient k b₀ s := «Σ».fullChart_functionField_smul k s r _
      _ = z := hr

set_option backward.isDefEq.respectTransparency.types false in
theorem actualChartTopCoefficient_injective
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) (s : «Σ».fullCones) :
    Function.Injective («Σ».actualChartTopCoefficient k b₀ s) := by
  intro ω η he
  apply (basisTopExteriorEquiv («Σ».actualFullChartDifferentialBasis k s)).injective
  apply «Σ».chartRationalMap_injective k («Σ».fullConeIndex s)
  apply mul_right_cancel₀ (Units.ne_zero («Σ».chartVolumeCoefficient k b₀ s))
  exact («Σ».actualChartTopCoefficient_apply k b₀ s ω).symm.trans
    (he.trans («Σ».actualChartTopCoefficient_apply k b₀ s η))

/-- The local character is computed from the actual differential volume.
This is the sign in the toric canonical divisor formula. -/
theorem canonical_cartierLatticePoint (s : «Σ».fullCones) :
    «Σ».cartierLatticePoint (fun _ => -1) s = ∑ i, «Σ».fullCharacterBasis s i := by
  simp only [cartierLatticePoint, neg_one_zsmul, Finset.sum_neg_distrib, neg_neg]
  rfl

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.actualChartTopCoefficient_basis

end
end Source_ToricFanDifferentials
-- END ORIGINAL PaperVerification.ToricFanDifferentials



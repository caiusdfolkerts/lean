module

public import PaperVerification.ToricIntrinsicDifferentialSheaf
public import PaperVerification.ToricRationalSheaf
public import PaperVerification.ToricModuleFrameGluing
public import Mathlib.AlgebraicGeometry.Modules.Tilde

@[expose] public section

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

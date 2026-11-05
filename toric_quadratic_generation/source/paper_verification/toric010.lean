module

public import Lean.Elab.BuiltinEvalCommand
public meta import Lean.Elab.BuiltinEvalCommand
public import Lean.Util.CollectAxioms
public meta import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public meta import Lean.Util.FoldConsts
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

@[expose] public section


-- BEGIN ORIGINAL PaperVerification.ToricRationalSheaf
section Source_ToricRationalSheaf

-- original header: module

-- original header: public import Mathlib.AlgebraicGeometry.FunctionField
-- original header: public import Mathlib.AlgebraicGeometry.Stalk
-- original header: public import Mathlib.AlgebraicGeometry.Modules.Sheaf
-- original header: public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
-- original header: public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
-- original header: public import Mathlib.Algebra.Category.Ring.Constructions

-- original header: @[expose] public section

/-!
# The actual sheaf of rational functions on an integral scheme

This is the pushforward of the structure module of the generic-point scheme.
Its sections on every nonempty open are identified with the actual function
field, compatibly with restriction and the structure sheaf.  These are scheme
and sheaf constructions; no fan, polytope, or divisor dictionary is assumed.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

/-- Evaluate a sheaf-of-modules morphism on an actual scheme open.  This
is the existing scheme-module evaluation, also available when elaboration
retains the underlying `SheafOfModules.Hom` type. -/
abbrev SheafOfModules.Hom.app {X : Scheme.{u}} {M N : X.Modules}
    (f : SheafOfModules.Hom M N) (U : X.Opens) : Γ(M,U) ⟶ Γ(N,U) :=
  Scheme.Modules.Hom.app f U

namespace PaperVerification.ToricSchemes

/-- The whole open of a nonempty scheme contains any chosen point. -/
instance nonempty_top_open (X : Scheme.{u}) [Nonempty X] : Nonempty (⊤ : X.Opens) :=
  ⟨⟨Classical.choice inferInstance, by trivial⟩⟩

variable (X : Scheme.{u}) [IsIntegral X]

/-- The actual generic-point morphism. -/
abbrev genericPointMap : Spec X.functionField ⟶ X :=
  X.fromSpecStalk (genericPoint X)

theorem genericPoint_mem_open (U : X.Opens) [Nonempty U] :
    genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
    (by simpa using (show Nonempty U from inferInstance))

@[simp] theorem germToFunctionField_restrict {U V : X.Opens}
    [Nonempty U] [Nonempty V] (i : V ⟶ U) (a : Γ(X,U)) :
    X.germToFunctionField V (X.presheaf.map i.op a) = X.germToFunctionField U a :=
  X.presheaf.germ_res_apply i (genericPoint X) (genericPoint_mem_open X V) a

@[simp] theorem genericPointMap_apply (z : Spec X.functionField) :
    genericPointMap X z = genericPoint X := by
  haveI : Subsingleton (Spec X.functionField) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum X.functionField))
  have hz : z = IsLocalRing.closedPoint X.functionField := Subsingleton.elim _ _
  subst z
  exact X.fromSpecStalk_closedPoint

@[simp] theorem genericPointMap_preimage (U : X.Opens) [Nonempty U] :
    genericPointMap X ⁻¹ᵁ U = ⊤ := by
  apply top_unique
  intro z _
  change genericPointMap X z ∈ U
  rw [genericPointMap_apply]
  exact genericPoint_mem_open X U

/-- The sheaf `j_* O_η`, where `η` is the generic point of `X`. -/
def rationalFunctions : X.Modules :=
  (Scheme.Modules.pushforward (genericPointMap X)).obj
    (SheafOfModules.unit (Spec X.functionField).ringCatSheaf)

/-- Evaluation of the pushforward ring sections in the function field. -/
def rationalSectionValueIso (U : X.Opens) [Nonempty U] :
    Γ(Spec X.functionField, genericPointMap X ⁻¹ᵁ U) ≅ X.functionField :=
  (Spec X.functionField).presheaf.mapIso
    (eqToIso (congrArg op (genericPointMap_preimage X U))) ≪≫
      Scheme.ΓSpecIso X.functionField

/-- The underlying additive equivalence on actual rational-function sections. -/
def rationalValue (U : X.Opens) [Nonempty U] :
    Γ(rationalFunctions X, U) ≃+ X.functionField :=
  (rationalSectionValueIso X U).commRingCatIsoToRingEquiv.toAddEquiv

@[simp] theorem rationalValue_zero (U : X.Opens) [Nonempty U] :
    rationalValue X U 0 = 0 := map_zero _

@[simp] theorem rationalValue_add (U : X.Opens) [Nonempty U]
    (s t : Γ(rationalFunctions X, U)) :
    rationalValue X U (s+t) = rationalValue X U s + rationalValue X U t := map_add _ _ _

theorem rationalSectionValueIso_naturality {U V : X.Opens}
    [Nonempty U] [Nonempty V] (i : V ⟶ U) :
    (Spec X.functionField).presheaf.map
        ((Opens.map (genericPointMap X).base).map i).op ≫
      (rationalSectionValueIso X V).hom = (rationalSectionValueIso X U).hom := by
  simp only [rationalSectionValueIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← Functor.map_comp]
  congr 1

/-- Restricting a rational function does not change its value in `K(X)`. -/
@[simp] theorem rationalValue_restrict {U V : X.Opens}
    [Nonempty U] [Nonempty V] (i : V ⟶ U) (s : Γ(rationalFunctions X, U)) :
    rationalValue X V ((rationalFunctions X).presheaf.map i.op s) =
      rationalValue X U s := by
  exact congrArg (fun f => f s) (rationalSectionValueIso_naturality X i)

/-- The canonical inclusion of regular functions in rational functions. -/
def regularToRational :
    (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ rationalFunctions X :=
  SheafOfModules.unitToPushforwardObjUnit (genericPointMap X).toRingCatSheafHom

theorem genericPointMap_app_value (U : X.Opens) [Nonempty U] :
    (genericPointMap X).app U ≫ (rationalSectionValueIso X U).hom =
      X.germToFunctionField U := by
  rw [Scheme.fromSpecStalk_app (genericPoint_mem_open X U)]
  simp only [rationalSectionValueIso, Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom,
    Category.assoc]
  have hcancel :
      (Spec X.functionField).presheaf.map (homOfLE le_top).op ≫
        (Spec X.functionField).presheaf.map
          (eqToHom (congrArg op (genericPointMap_preimage X U))) = 𝟙 _ := by
    rw [← Functor.map_comp]
    convert (Spec X.functionField).presheaf.map_id (op ⊤) using 1
  rw [← Category.assoc _ _ (Scheme.ΓSpecIso X.functionField).hom,
    hcancel, Category.id_comp, Iso.inv_hom_id, Category.comp_id]

@[simp] theorem regularToRational_value (U : X.Opens) [Nonempty U]
    (a : Γ(X,U)) :
    rationalValue X U ((regularToRational X).app U a) =
      X.germToFunctionField U a := by
  exact congrArg (fun f => f a) (genericPointMap_app_value X U)

/-- The section equivalence respects the actual structure-sheaf scalar action. -/
theorem rationalValue_smul (U : X.Opens) [Nonempty U]
    (a : Γ(X,U)) (s : Γ(rationalFunctions X,U)) :
    rationalValue X U (a • s) =
      X.germToFunctionField U a * rationalValue X U s := by
  change (rationalSectionValueIso X U).hom
      ((genericPointMap X).app U a *
        (show Γ(Spec X.functionField, genericPointMap X ⁻¹ᵁ U) from s)) = _
  rw [map_mul]
  congr 1
  exact regularToRational_value X U a

set_option backward.isDefEq.respectTransparency false in
/-- Rational sections are the function field as a module over regular sections. -/
def rationalValueLinearEquiv (U : X.Opens) [Nonempty U] :
    Γ(rationalFunctions X,U) ≃ₗ[Γ(X,U)] X.functionField where
  __ := rationalValue X U
  map_smul' a s := by
    change rationalValue X U (a • s) =
      X.germToFunctionField U a * rationalValue X U s
    exact rationalValue_smul X U a s

theorem regularSections_subsingleton_of_empty (U : X.Opens) (hU : U=⊥) :
    Subsingleton Γ(X,U) :=
  CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hU)

set_option backward.isDefEq.respectTransparency false in
/-- The regular-to-rational map is injective on every actual open set,
including the empty set. -/
theorem regularToRational_injective (U : X.Opens) :
    Function.Injective ((regularToRational X).app U) := by
  classical
  by_cases hU : Nonempty U
  · letI := hU
    intro a b hab
    apply X.germToFunctionField_injective U
    exact (regularToRational_value X U a).symm.trans
      ((congrArg (rationalValue X U) hab).trans (regularToRational_value X U b))
  · have hbot : U=⊥ := by
      apply le_antisymm
      · intro x hx
        exact (hU ⟨⟨x,hx⟩⟩).elim
      · exact bot_le
    letI := regularSections_subsingleton_of_empty X U hbot
    exact fun (a b : Γ(X,U)) _ => Subsingleton.elim a b

instance regularToRational_mono : Mono (regularToRational X) := by
  haveI : Mono (regularToRational X).val :=
    PresheafOfModules.mono_of_injective (fun {U} => regularToRational_injective X U.unop)
  exact (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map
    (inferInstanceAs (Mono (regularToRational X).val))

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.rationalValueLinearEquiv
#print axioms PaperVerification.ToricSchemes.regularToRational_injective
end
end Source_ToricRationalSheaf
-- END ORIGINAL PaperVerification.ToricRationalSheaf


-- BEGIN ORIGINAL PaperVerification.ToricCartierSheaf
section Source_ToricCartierSheaf

-- original header: module

-- original header: public import PaperVerification.ToricRationalSheaf
-- original header: public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

-- original header: @[expose] public section

/-!
# Cartier data as actual invertible fractional sheaves

The objects in this file are sheaves on an integral scheme, embedded in the
actual rational-function sheaf.  Local rank one is expressed by isomorphisms
on the open subsite.  No fan, positivity, polytope, or global-section formula
is included in the definition.  Local rational generators are derived from
the sheaf trivializations and the injective embedding.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

namespace PaperVerification.ToricSchemes

variable {X : Scheme.{u}} [IsIntegral X]

/-- Local rank one on the actual open subsite. The category is the category
of actual sheaves of modules, and the target is the structure module. -/
def IsInvertibleModule (M : X.Modules) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty (M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))

theorem isInvertibleModule_unit :
    IsInvertibleModule (SheafOfModules.unit X.ringCatSheaf : X.Modules) := by
  intro x
  exact ⟨⊤, trivial, ⟨Iso.refl _⟩⟩

theorem isInvertibleModule_of_iso {M N : X.Modules} (e : M ≅ N)
    (hM : IsInvertibleModule M) : IsInvertibleModule N := by
  intro x
  obtain ⟨U,hx,⟨t⟩⟩ := hM x
  exact ⟨U,hx,⟨(SheafOfModules.overFunctor X.ringCatSheaf U).mapIso e.symm ≪≫ t⟩⟩

/-- An invertible fractional sheaf. The injective morphism records the
embedding into rational functions, so changing it by a rational unit changes
the Cartier divisor while leaving the underlying invertible module isomorphic.

Two such presentations are identified below only when their embeddings agree.
This is the usual fractional-sheaf presentation of a Cartier divisor. -/
structure CartierData (X : Scheme.{u}) [IsIntegral X] where
  sheaf : X.Modules
  inclusion : sheaf ⟶ rationalFunctions X
  inclusion_injective : ∀ U : X.Opens, Function.Injective (inclusion.app U)
  locallyFree : IsInvertibleModule sheaf

namespace CartierData

variable (D E F : CartierData X)

/-- The zero divisor, represented by the actual structure module. -/
def zero (X : Scheme.{u}) [IsIntegral X] : CartierData X where
  sheaf := SheafOfModules.unit X.ringCatSheaf
  inclusion := regularToRational X
  inclusion_injective := regularToRational_injective X
  locallyFree := isInvertibleModule_unit

/-- Equivalence of fractional-sheaf presentations preserves the rational
embedding, not only the abstract isomorphism class of the line bundle. -/
def Equivalent : Prop :=
  ∃ e : D.sheaf ≅ E.sheaf, e.hom ≫ E.inclusion = D.inclusion

theorem equivalent_refl : D.Equivalent D := ⟨Iso.refl _, by simp⟩

theorem equivalent_symm (h : D.Equivalent E) : E.Equivalent D := by
  obtain ⟨e,he⟩ := h
  refine ⟨e.symm,?_⟩
  rw [← he, Iso.symm_hom, Iso.inv_hom_id_assoc]

theorem equivalent_trans (hDE : D.Equivalent E) (hEF : E.Equivalent F) :
    D.Equivalent F := by
  obtain ⟨e,he⟩ := hDE
  obtain ⟨f,hf⟩ := hEF
  exact ⟨e ≪≫ f, by simpa only [Iso.trans_hom, Category.assoc, hf] using he⟩

instance presentationSetoid : Setoid (CartierData X) where
  r := Equivalent
  iseqv := ⟨equivalent_refl, fun {_ _} h => equivalent_symm _ _ h,
    fun {_ _ _} hDE hEF => equivalent_trans _ _ _ hDE hEF⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
/-- Values of actual sections in the function field. -/
def sectionValue (U : X.Opens) [Nonempty U] :
    Γ(D.sheaf,U) →ₗ[Γ(X,U)] X.functionField :=
  (rationalValueLinearEquiv X U).toLinearMap.comp
    (D.inclusion.val.app (op U)).hom

@[simp] theorem sectionValue_apply (U : X.Opens) [Nonempty U]
    (s : Γ(D.sheaf,U)) :
    D.sectionValue U s = rationalValue X U (D.inclusion.app U s) := rfl

theorem sectionValue_injective (U : X.Opens) [Nonempty U] :
    Function.Injective (D.sectionValue U) :=
  (rationalValue X U).injective.comp (D.inclusion_injective U)

@[simp] theorem sectionValue_smul (U : X.Opens) [Nonempty U]
    (a : Γ(X,U)) (s : Γ(D.sheaf,U)) :
    D.sectionValue U (a • s) = X.germToFunctionField U a * D.sectionValue U s := by
  simp only [sectionValue_apply, Scheme.Modules.Hom.app_smul, rationalValue_smul]

@[simp] theorem sectionValue_restrict {U V : X.Opens}
    [Nonempty U] [Nonempty V] (i : V ⟶ U) (s : Γ(D.sheaf,U)) :
    D.sectionValue V (D.sheaf.presheaf.map i.op s) = D.sectionValue U s := by
  have hn := congrArg (fun f => f s) (D.inclusion.mapPresheaf.naturality i.op)
  change D.inclusion.app V (D.sheaf.presheaf.map i.op s) =
    (rationalFunctions X).presheaf.map i.op (D.inclusion.app U s) at hn
  simp only [sectionValue_apply, hn, rationalValue_restrict]

/-- The actual image of the module of sections in `K(X)`. -/
def sectionValueRange (U : X.Opens) [Nonempty U] :
    Submodule Γ(X,U) X.functionField := (D.sectionValue U).range

theorem equivalent_sectionValueRange (h : D.Equivalent E)
    (U : X.Opens) [Nonempty U] : D.sectionValueRange U = E.sectionValueRange U := by
  obtain ⟨e,he⟩ := h
  have hval (s : Γ(D.sheaf,U)) :
      E.sectionValue U (e.hom.app U s) = D.sectionValue U s := by
    change rationalValue X U (E.inclusion.app U (e.hom.app U s)) = _
    have hh := congrArg (fun f => f.app U s) he
    simpa only [sectionValue_apply, Scheme.Modules.Hom.comp_app,
      ConcreteCategory.comp_apply] using
      congrArg (rationalValue X U) hh
  ext r
  constructor
  · rintro ⟨s,rfl⟩
    exact ⟨e.hom.app U s,hval s⟩
  · rintro ⟨s,rfl⟩
    refine ⟨e.inv.app U s,?_⟩
    rw [← hval]
    have hi : e.hom.app U (e.inv.app U s)=s := by
      simpa only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app,
        ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using
        congrArg (fun f => f.app U s) e.inv_hom_id
    rw [hi]

/-- A chosen local trivialization over an actual open subsite. -/
abbrev Frame (U : X.Opens) :=
  D.sheaf.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)

/-- The local coordinate isomorphism on a smaller open. -/
def frameLinearEquiv {U : X.Opens} (e : D.Frame U) (V : X.Opens) (hVU : V≤U) :
    Γ(D.sheaf,V) ≃ₗ[Γ(X,V)] Γ(X,V) :=
  ((PresheafOfModules.evaluation (X.ringCatSheaf.over U).obj
      (op (Over.mk (homOfLE hVU)))).mapIso
        ((SheafOfModules.forget _).mapIso e)).toLinearEquiv

/-- The actual local section corresponding to the regular function one. -/
def frameGenerator {U : X.Opens} (e : D.Frame U) (V : X.Opens) (hVU : V≤U) :
    Γ(D.sheaf,V) := (D.frameLinearEquiv e V hVU).symm 1

theorem section_eq_smul_frameGenerator {U : X.Opens} (e : D.Frame U)
    (V : X.Opens) (hVU : V≤U) (s : Γ(D.sheaf,V)) :
    s = D.frameLinearEquiv e V hVU s • D.frameGenerator e V hVU := by
  apply (D.frameLinearEquiv e V hVU).injective
  simp [frameGenerator]

theorem frameGenerator_ne_zero {U : X.Opens} (e : D.Frame U)
    (V : X.Opens) [Nonempty V] (hVU : V≤U) :
    D.frameGenerator e V hVU ≠ 0 := by
  intro hz
  have h1 : (1 : Γ(X,V))=0 := by
    have h := congrArg (D.frameLinearEquiv e V hVU) hz
    simpa only [frameGenerator, LinearEquiv.apply_symm_apply, map_zero] using h
  have hfield : (1 : X.functionField)=0 := by
    simpa using congrArg (X.germToFunctionField V) h1
  exact one_ne_zero hfield

set_option backward.isDefEq.respectTransparency false in
theorem frameGenerator_restrict {U V : X.Opens} (e : D.Frame U) (hVU : V≤U) :
    D.sheaf.presheaf.map (homOfLE hVU).op (D.frameGenerator e U le_rfl) =
      D.frameGenerator e V hVU := by
  let i : Over.mk (homOfLE hVU) ⟶ Over.mk (𝟙 U) :=
    Over.homMk (homOfLE hVU) (by simp)
  have h := PresheafOfModules.naturality_apply e.inv.val i.op (1 : Γ(X,U))
  change D.sheaf.presheaf.map (homOfLE hVU).op
      (e.inv.val.app (op (Over.mk (𝟙 U))) (1 : Γ(X,U))) =
    e.inv.val.app (op (Over.mk (homOfLE hVU))) (1 : Γ(X,V))
  change e.inv.val.app (op (Over.mk (homOfLE hVU)))
      (X.presheaf.map (homOfLE hVU).op (1 : Γ(X,U))) =
    D.sheaf.presheaf.map (homOfLE hVU).op
      (e.inv.val.app (op (Over.mk (𝟙 U))) (1 : Γ(X,U))) at h
  simpa only [map_one] using h.symm

/-- The rational generator attached to a local frame is a nonzero element of
the actual function field. Its inverse is the local Cartier equation. -/
def frameRationalGenerator {U : X.Opens} [Nonempty U] (e : D.Frame U) :
    X.functionField := D.sectionValue U (D.frameGenerator e U le_rfl)

theorem frameRationalGenerator_ne_zero {U : X.Opens} [Nonempty U] (e : D.Frame U) :
    D.frameRationalGenerator e ≠ 0 := by
  intro h
  have hz := (D.sectionValue_injective U) (h.trans (map_zero _).symm)
  exact D.frameGenerator_ne_zero e U le_rfl hz

theorem sectionValue_frameGenerator {U V : X.Opens}
    [Nonempty U] [Nonempty V] (e : D.Frame U) (hVU : V≤U) :
    D.sectionValue V (D.frameGenerator e V hVU) = D.frameRationalGenerator e := by
  rw [← D.frameGenerator_restrict e hVU, D.sectionValue_restrict]
  rfl

/-- Exact local fractional-principal description, derived from actual sheaf
triviality. No combinatorial section formula occurs in the hypotheses. -/
theorem mem_sectionValueRange_iff {U V : X.Opens}
    [Nonempty U] [Nonempty V] (e : D.Frame U) (hVU : V≤U) (r : X.functionField) :
    r ∈ D.sectionValueRange V ↔
      ∃ a : Γ(X,V), X.germToFunctionField V a * D.frameRationalGenerator e = r := by
  constructor
  · rintro ⟨s,rfl⟩
    refine ⟨D.frameLinearEquiv e V hVU s,?_⟩
    conv_rhs => rw [D.section_eq_smul_frameGenerator e V hVU s]
    rw [D.sectionValue_smul, D.sectionValue_frameGenerator]
  · rintro ⟨a,ha⟩
    refine ⟨a • D.frameGenerator e V hVU,?_⟩
    rw [D.sectionValue_smul, D.sectionValue_frameGenerator, ha]

/-- Two actual local generators differ by a unit of the regular-function
ring on every nonempty overlap. This recovers the usual Cartier cocycle
condition from the fractional-sheaf definition. -/
theorem exists_frameTransitionUnit {U W V : X.Opens}
    [Nonempty U] [Nonempty W] [Nonempty V]
    (e : D.Frame U) (f : D.Frame W) (hVU : V≤U) (hVW : V≤W) :
    ∃ a : Γ(X,V)ˣ, X.germToFunctionField V (a : Γ(X,V)) =
      D.frameRationalGenerator e / D.frameRationalGenerator f := by
  have hq : D.frameRationalGenerator e ∈ D.sectionValueRange V :=
    ⟨D.frameGenerator e V hVU,D.sectionValue_frameGenerator e hVU⟩
  have hr : D.frameRationalGenerator f ∈ D.sectionValueRange V :=
    ⟨D.frameGenerator f V hVW,D.sectionValue_frameGenerator f hVW⟩
  obtain ⟨a,ha⟩ := (D.mem_sectionValueRange_iff f hVW _).mp hq
  obtain ⟨b,hb⟩ := (D.mem_sectionValueRange_iff e hVU _).mp hr
  have hab : a*b=1 := by
    apply X.germToFunctionField_injective V
    rw [map_mul, map_one]
    apply mul_right_cancel₀ (D.frameRationalGenerator_ne_zero e)
    rw [mul_assoc,hb,ha,one_mul]
  let aUnit : Γ(X,V)ˣ := ⟨a,b,hab,by simpa only [mul_comm] using hab⟩
  refine ⟨aUnit,?_⟩
  exact (eq_div_iff (D.frameRationalGenerator_ne_zero f)).mpr ha

/-- The transition unit is uniquely determined by its rational value. -/
theorem frameTransitionUnit_unique {U W V : X.Opens}
    [Nonempty U] [Nonempty W] [Nonempty V]
    (e : D.Frame U) (f : D.Frame W) {a b : Γ(X,V)ˣ}
    (ha : X.germToFunctionField V (a : Γ(X,V)) =
      D.frameRationalGenerator e / D.frameRationalGenerator f)
    (hb : X.germToFunctionField V (b : Γ(X,V)) =
      D.frameRationalGenerator e / D.frameRationalGenerator f) : a=b := by
  apply Units.ext
  exact X.germToFunctionField_injective V (ha.trans hb.symm)

/-- The regular unit cocycle follows from multiplication in the actual
function field and injectivity of regular functions. -/
theorem frameTransitionUnit_cocycle {U V W Z : X.Opens}
    [Nonempty U] [Nonempty V] [Nonempty W] [Nonempty Z]
    (e : D.Frame U) (f : D.Frame V) (g : D.Frame W)
    (a b c : Γ(X,Z)ˣ)
    (ha : X.germToFunctionField Z (a : Γ(X,Z)) =
      D.frameRationalGenerator e / D.frameRationalGenerator f)
    (hb : X.germToFunctionField Z (b : Γ(X,Z)) =
      D.frameRationalGenerator f / D.frameRationalGenerator g)
    (hc : X.germToFunctionField Z (c : Γ(X,Z)) =
      D.frameRationalGenerator e / D.frameRationalGenerator g) : a*b=c := by
  apply Units.ext
  apply X.germToFunctionField_injective Z
  simp only [Units.val_mul,map_mul,ha,hb,hc]
  field_simp [D.frameRationalGenerator_ne_zero f,
    D.frameRationalGenerator_ne_zero g]

end CartierData

/-- Cartier divisors as fractional invertible sheaves modulo their actual
embedded isomorphisms. The definition does not identify principal divisors
with zero; doing so would give the Picard group instead. -/
def CartierDivisor (X : Scheme.{u}) [IsIntegral X] :=
  Quotient (CartierData.presentationSetoid (X:=X))

namespace CartierDivisor

def ofData (D : CartierData X) : CartierDivisor X := Quotient.mk _ D

theorem ofData_eq_iff (D E : CartierData X) :
    ofData D = ofData E ↔ D.Equivalent E := Quotient.eq

end CartierDivisor

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.CartierData.mem_sectionValueRange_iff
#print axioms PaperVerification.ToricSchemes.CartierDivisor.ofData_eq_iff
end
end Source_ToricCartierSheaf
-- END ORIGINAL PaperVerification.ToricCartierSheaf


-- BEGIN ORIGINAL PaperVerification.ToricRegularRational
section Source_ToricRegularRational

-- original header: module

-- original header: public import PaperVerification.ToricRationalSheaf
-- original header: public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

-- original header: @[expose] public section

/-!
# Local regularity of actual rational functions

A rational function on an integral scheme is a regular section on an open
set exactly when it belongs to each local ring there. The reverse direction
is proved by taking local representatives and applying the actual structure
sheaf gluing axiom.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace PaperVerification.ToricSchemes

variable (X : Scheme.{u}) [IsIntegral X]

/-- The actual local ring, embedded in the actual function field. -/
def regularAtSubring (x : X) : Subring X.functionField :=
  (algebraMap (X.presheaf.stalk x) X.functionField).range

theorem regular_germ_mem_regularAt (U : X.Opens) [Nonempty U]
    (s : Γ(X,U)) (x : X) (hx : x∈U) :
    X.germToFunctionField U s ∈ regularAtSubring X x :=
  ⟨X.presheaf.germ U x hx s,X.algebraMap_germ_eq_germToFunctionField hx s⟩

set_option backward.isDefEq.respectTransparency false in
/-- The direction from stalkwise regularity to an actual regular section. -/
theorem exists_regularSection_of_stalkwise (U : X.Opens) [Nonempty U]
    (r : X.functionField) (hr : ∀ x∈U, r∈regularAtSubring X x) :
    ∃ s : Γ(X,U), X.germToFunctionField U s = r := by
  classical
  have hUne : Nonempty U := inferInstance
  have hloc : ∀ x : U, ∃ V : X.Opens, V≤U ∧ x.val∈V ∧
      ∃ s : Γ(X,V), ∀ hV : Nonempty V,
        @Scheme.germToFunctionField X inferInstance V hV s = r := by
    intro x
    obtain ⟨t,ht⟩ := hr x x.property
    obtain ⟨W,hxW,s,hs⟩ := X.presheaf.exists_germ_eq t
    let V : X.Opens := W⊓U
    have hxV : x.val∈V := ⟨hxW,x.property⟩
    let sV : Γ(X,V) := X.presheaf.map (homOfLE inf_le_left).op s
    refine ⟨V,inf_le_right,hxV,sV,?_⟩
    intro hV
    letI := hV
    rw [← X.algebraMap_germ_eq_germToFunctionField hxV sV]
    change algebraMap (X.presheaf.stalk x.val) X.functionField
      (X.presheaf.germ V x.val hxV
        (X.presheaf.map (homOfLE inf_le_left).op s)) = r
    rw [X.presheaf.germ_res_apply,hs,ht]
  choose V hVU hxV s hs using hloc
  letI (x : U) : Nonempty (V x) := ⟨⟨x.val,hxV x⟩⟩
  have hcover : U≤⨆ x : U, V x := by
    intro x hx
    exact Opens.mem_iSup.mpr ⟨⟨x,hx⟩,hxV ⟨x,hx⟩⟩
  have hcompatible : X.presheaf.IsCompatible V s := by
    intro x y
    letI : Nonempty (V x⊓V y : X.Opens) :=
      ⟨⟨genericPoint X,genericPoint_mem_open X (V x),
        genericPoint_mem_open X (V y)⟩⟩
    apply X.germToFunctionField_injective (V x⊓V y)
    rw [germToFunctionField_restrict,germToFunctionField_restrict]
    exact (hs x inferInstance).trans (hs y inferInstance).symm
  obtain ⟨g,hg,-⟩ := X.sheaf.existsUnique_gluing' V U
    (fun x => homOfLE (hVU x)) hcover s hcompatible
  refine ⟨g,?_⟩
  let x : U := Classical.choice hUne
  calc
    X.germToFunctionField U g =
      X.germToFunctionField (V x) (X.presheaf.map (homOfLE (hVU x)).op g) :=
        (germToFunctionField_restrict X _ g).symm
    _ = X.germToFunctionField (V x) (s x) := congrArg _ (hg x)
    _ = r := hs x inferInstance

/-- Exact local-to-global regularity, with no normality or affine assumption. -/
theorem mem_regular_range_iff_stalkwise (U : X.Opens) [Nonempty U]
    (r : X.functionField) :
    r ∈ (X.germToFunctionField U).hom.range ↔
      ∀ x∈U, r∈regularAtSubring X x := by
  constructor
  · rintro ⟨s,rfl⟩ x hx
    exact regular_germ_mem_regularAt X U s x hx
  · exact exists_regularSection_of_stalkwise X U r

theorem regular_unit_iff_stalkwise (U : X.Opens) [Nonempty U]
    (r : X.functionField) (hr : r≠0) :
    (∃ s : Γ(X,U)ˣ, X.germToFunctionField U (s : Γ(X,U))=r) ↔
      (∀ x∈U, r∈regularAtSubring X x) ∧
      (∀ x∈U, r⁻¹∈regularAtSubring X x) := by
  constructor
  · rintro ⟨s,hs⟩
    refine ⟨?_,?_⟩
    · rw [← hs]
      exact regular_germ_mem_regularAt X U s
    · have hinv : X.germToFunctionField U ((s⁻¹ : Γ(X,U)ˣ) : Γ(X,U))=r⁻¹ := by
        have hmul := congrArg (X.germToFunctionField U) s.val_inv
        rw [map_mul,map_one,hs] at hmul
        apply mul_left_cancel₀ hr
        rw [mul_inv_cancel₀ hr]
        exact hmul
      rw [← hinv]
      exact regular_germ_mem_regularAt X U (s⁻¹ : Γ(X,U)ˣ)
  · rintro ⟨h,hInv⟩
    obtain ⟨s,hs⟩ := exists_regularSection_of_stalkwise X U r h
    obtain ⟨t,ht⟩ := exists_regularSection_of_stalkwise X U r⁻¹ hInv
    have hst : s*t=1 := by
      apply X.germToFunctionField_injective U
      rw [map_mul,map_one,hs,ht,mul_inv_cancel₀ hr]
    exact ⟨⟨s,t,hst,by simpa only [mul_comm] using hst⟩,hs⟩

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.mem_regular_range_iff_stalkwise
#print axioms PaperVerification.ToricSchemes.regular_unit_iff_stalkwise
end
end Source_ToricRegularRational
-- END ORIGINAL PaperVerification.ToricRegularRational


-- BEGIN ORIGINAL PaperVerification.ToricCartierCocycle
section Source_ToricCartierCocycle

-- original header: module

-- original header: public import PaperVerification.ToricCartierSheaf
-- original header: public import PaperVerification.ToricRegularRational
-- original header: public import Mathlib.Algebra.Module.Submodule.Equiv

-- original header: @[expose] public section

/-!
# Construction of a fractional sheaf from genuine Cartier equations

The input consists only of an open cover, nonzero rational local generators,
and their regular-unit transition condition. Membership in the resulting
subsheaf is a pointwise condition in the actual local rings. The sheaf axiom
is proved from locality; local principalness is then proved using gluing of
regular functions. No global-section or polytope assertion is assumed.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace PaperVerification.ToricSchemes

variable (X : Scheme.{u}) [IsIntegral X]

/-- Rational evaluation using a specified point to witness nonemptiness. -/
def rationalValueAt (U : X.Opens) (x : U) :
    Γ(rationalFunctions X,U) →+ X.functionField := by
  letI : Nonempty U := ⟨x⟩
  exact (rationalValue X U).toAddMonoidHom

@[simp] theorem rationalValueAt_eq (U : X.Opens) [Nonempty U] (x : U)
    (s : Γ(rationalFunctions X,U)) :
    rationalValueAt X U x s = rationalValue X U s := rfl

theorem rationalValueAt_restrict {U V : X.Opens} (i : V ⟶ U)
    (x : V) (s : Γ(rationalFunctions X,U)) :
    rationalValueAt X V x ((rationalFunctions X).presheaf.map i.op s) =
      rationalValueAt X U ⟨x.val,i.le x.property⟩ s := by
  letI : Nonempty V := ⟨x⟩
  letI : Nonempty U := ⟨⟨x.val,i.le x.property⟩⟩
  exact rationalValue_restrict X i s

/-- Usual rational Cartier transition data, with local generators for O(D).
The ratio of any two generators is regular at every point in their overlap;
the reverse ordered pair gives its regular inverse. -/
structure RationalCartierCocycle where
  index : Type u
  openSet : index → X.Opens
  covers : ∀ x : X, ∃ i, x∈openSet i
  generator : index → X.functionFieldˣ
  transition : ∀ i j (x : X), x∈openSet i → x∈openSet j →
    ((generator i : X.functionField)/(generator j : X.functionField)) ∈
      regularAtSubring X x

namespace RationalCartierCocycle

variable {X} (C : RationalCartierCocycle X)

/-- A rational section belongs to O(D) precisely when division by each local
generator is regular in each relevant actual local ring. -/
def IsSection (U : X.Opens) (s : Γ(rationalFunctions X,U)) : Prop :=
  ∀ i (x : U), x.val∈C.openSet i →
    rationalValueAt X U x s / (C.generator i : X.functionField) ∈
      regularAtSubring X x.val

set_option backward.isDefEq.respectTransparency false in
/-- Local Cartier regularity is a submodule of the actual rational sections. -/
def sectionSubmodule (U : X.Opens) :
    Submodule Γ(X,U) Γ(rationalFunctions X,U) where
  carrier := {s | C.IsSection U s}
  zero_mem' := by
    intro i x hx
    letI : Nonempty U := ⟨x⟩
    change rationalValue X U 0 / (C.generator i : X.functionField) ∈
      regularAtSubring X x.val
    rw [rationalValue_zero, zero_div]
    exact (regularAtSubring X x.val).zero_mem
  add_mem' := by
    intro s t hs ht i x hx
    letI : Nonempty U := ⟨x⟩
    change rationalValue X U (s+t) / (C.generator i : X.functionField) ∈
      regularAtSubring X x.val
    rw [rationalValue_add, add_div]
    exact (regularAtSubring X x.val).add_mem (hs i x hx) (ht i x hx)
  smul_mem' := by
    intro a s hs i x hx
    letI : Nonempty U := ⟨x⟩
    change rationalValue X U (a • s) / (C.generator i : X.functionField) ∈
      regularAtSubring X x.val
    rw [rationalValue_smul, mul_div_assoc]
    exact (regularAtSubring X x.val).mul_mem
      (regular_germ_mem_regularAt X U a x.val x.property) (hs i x hx)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def presheafSubmodule : (rationalFunctions X).val.Submodule where
  obj U := C.sectionSubmodule U.unop
  map {U V} f := by
    intro s hs i x hx
    change rationalValueAt X V.unop x
      ((rationalFunctions X).presheaf.map f s) /
        (C.generator i : X.functionField) ∈ regularAtSubring X x.val
    have hval := rationalValueAt_restrict X f.unop x
      (show Γ(rationalFunctions X,U.unop) from s)
    exact (congrArg (fun r : X.functionField =>
      r / (C.generator i : X.functionField) ∈ regularAtSubring X x.val) hval).mpr
        (hs i ⟨x.val,f.unop.le x.property⟩ hx)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The local membership condition is a sheaf condition on the actual
rational-function sheaf. -/
def sheafSubmodule : (rationalFunctions X).Submodule where
  toSubmodule := C.presheafSubmodule
  isSheaf {U} s hs := by
    intro i x hx
    obtain ⟨V,f,hf,hxV⟩ := hs x.val x.property
    have hlocal : C.IsSection V ((rationalFunctions X).presheaf.map f.op s) := hf
    have h := hlocal i ⟨x.val,hxV⟩ hx
    exact (congrArg (fun r : X.functionField =>
      r / (C.generator i : X.functionField) ∈ regularAtSubring X x.val)
        (rationalValueAt_restrict X f ⟨x.val,hxV⟩ s)).mp h

/-- The actual sheaf obtained from the local rational Cartier equations. -/
def sheaf : X.Modules := C.sheafSubmodule.toSheafOfModules

/-- Its actual inclusion in rational functions. -/
def inclusion : C.sheaf ⟶ rationalFunctions X := C.sheafSubmodule.ι

theorem inclusion_injective (U : X.Opens) :
    Function.Injective (C.inclusion.app U) := Subtype.val_injective

theorem mem_submodule_iff_local (i : C.index) (V : X.Opens) [Nonempty V]
    (hVi : V≤C.openSet i) (s : Γ(rationalFunctions X,V)) :
    s ∈ C.presheafSubmodule.obj (op V) ↔
      rationalValue X V s / (C.generator i : X.functionField) ∈
        (X.germToFunctionField V).hom.range := by
  rw [mem_regular_range_iff_stalkwise]
  constructor
  · intro hs x hx
    exact hs i ⟨x,hx⟩ (hVi hx)
  · intro hs j x hxj
    have hi := hs x.val x.property
    have ht := C.transition i j x.val (hVi x.property) hxj
    have he : (rationalValue X V s / (C.generator i : X.functionField)) *
        ((C.generator i : X.functionField)/(C.generator j : X.functionField)) =
        rationalValue X V s / (C.generator j : X.functionField) := by
      field_simp [Units.ne_zero]
    simpa only [rationalValueAt_eq,he] using
      (regularAtSubring X x.val).mul_mem hi ht

set_option backward.isDefEq.respectTransparency.types false in
/-- Division by a local rational generator, as an actual linear map on
sections of the constructed sheaf. -/
def dividedValue (i : C.index) (V : X.Opens) [Nonempty V] :
    Γ(C.sheaf,V) →ₗ[Γ(X,V)] X.functionField :=
  (LinearMap.mulRight Γ(X,V) ((C.generator i : X.functionField)⁻¹)).comp
    ((rationalValueLinearEquiv X V).toLinearMap.comp
      (C.sectionSubmodule V).subtype)

@[simp] theorem dividedValue_apply (i : C.index) (V : X.Opens) [Nonempty V]
    (s : Γ(C.sheaf,V)) :
    C.dividedValue i V s = rationalValue X V s.val / (C.generator i : X.functionField) := by
  rfl

theorem dividedValue_injective (i : C.index) (V : X.Opens) [Nonempty V] :
    Function.Injective (C.dividedValue i V) := by
  intro s t h
  apply Subtype.ext
  apply (rationalValue X V).injective
  exact (div_left_inj' (Units.ne_zero (C.generator i))).mp h

/-- The regular-section map as a linear map into the function field. -/
def regularValueLinearMap (V : X.Opens) [Nonempty V] :
    Γ(X,V) →ₗ[Γ(X,V)] X.functionField := Algebra.linearMap Γ(X,V) X.functionField

theorem dividedValue_range (i : C.index) (V : X.Opens) [Nonempty V]
    (hVi : V≤C.openSet i) :
    (C.dividedValue i V).range = (regularValueLinearMap V).range := by
  ext r
  constructor
  · rintro ⟨s,rfl⟩
    exact (C.mem_submodule_iff_local i V hVi s.val).mp s.property
  · rintro ⟨a,rfl⟩
    let s : Γ(rationalFunctions X,V) :=
      (rationalValue X V).symm
        (X.germToFunctionField V a * (C.generator i : X.functionField))
    have hs : s ∈ C.presheafSubmodule.obj (op V) := by
      apply (C.mem_submodule_iff_local i V hVi s).mpr
      refine ⟨a,?_⟩
      simp [s,Units.ne_zero]
    refine ⟨⟨s,hs⟩,?_⟩
    change rationalValue X V s / (C.generator i : X.functionField) =
      X.germToFunctionField V a
    simp [s,Units.ne_zero]

/-- Local coordinates, with the existence and uniqueness of the regular
coefficient proved by actual regular-function gluing. -/
def localCoordinatesNonempty (i : C.index) (V : X.Opens) [Nonempty V]
    (hVi : V≤C.openSet i) : Γ(C.sheaf,V) ≃ₗ[Γ(X,V)] Γ(X,V) :=
  (LinearEquiv.ofInjective (C.dividedValue i V) (C.dividedValue_injective i V)).trans
    ((LinearEquiv.ofEq _ _ (C.dividedValue_range i V hVi)).trans
      (LinearEquiv.ofInjective (regularValueLinearMap V)
        (X.germToFunctionField_injective V)).symm)

set_option backward.isDefEq.respectTransparency.types false in
theorem localCoordinatesNonempty_value (i : C.index) (V : X.Opens) [Nonempty V]
    (hVi : V≤C.openSet i) (s : Γ(C.sheaf,V)) :
    X.germToFunctionField V (C.localCoordinatesNonempty i V hVi s) =
      rationalValue X V s.val / (C.generator i : X.functionField) := by
  exact LinearEquiv.ofInjective_symm_apply (regularValueLinearMap V)
    (h := X.germToFunctionField_injective V)
    ((LinearEquiv.ofEq _ _ (C.dividedValue_range i V hVi))
      ((LinearEquiv.ofInjective (C.dividedValue i V)
        (C.dividedValue_injective i V)) s))

/-- Local coordinates on every open, with the uniquely determined map on
the empty open. -/
def localCoordinates (i : C.index) (V : X.Opens) (hVi : V≤C.openSet i) :
    Γ(C.sheaf,V) ≃ₗ[Γ(X,V)] Γ(X,V) := by
  classical
  by_cases hV : Nonempty V
  · letI := hV
    exact C.localCoordinatesNonempty i V hVi
  · have hbot : V=⊥ := by
      apply le_antisymm
      · intro x hx
        exact False.elim (hV ⟨⟨x,hx⟩⟩)
      · exact bot_le
    letI := regularSections_subsingleton_of_empty X V hbot
    letI := Module.subsingleton Γ(X,V) Γ(C.sheaf,V)
    exact LinearEquiv.ofSubsingleton _ _

@[simp] theorem localCoordinates_of_nonempty (i : C.index) (V : X.Opens)
    [Nonempty V] (hVi : V≤C.openSet i) :
    C.localCoordinates i V hVi = C.localCoordinatesNonempty i V hVi := by
  simp only [localCoordinates,dif_pos (show Nonempty V from inferInstance)]

theorem localCoordinates_value (i : C.index) (V : X.Opens) [Nonempty V]
    (hVi : V≤C.openSet i) (s : Γ(C.sheaf,V)) :
    X.germToFunctionField V (C.localCoordinates i V hVi s) =
      rationalValue X V s.val / (C.generator i : X.functionField) := by
  rw [localCoordinates_of_nonempty,localCoordinatesNonempty_value]

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual regular coordinates commute with restriction. -/
theorem localCoordinates_restrict (i : C.index) {V W : X.Opens}
    (f : W ⟶ V) (hVi : V≤C.openSet i) (hWi : W≤C.openSet i)
    (s : Γ(C.sheaf,V)) :
    C.localCoordinates i W hWi (C.sheaf.presheaf.map f.op s) =
      X.presheaf.map f.op (C.localCoordinates i V hVi s) := by
  classical
  by_cases hW : Nonempty W
  · letI := hW
    letI : Nonempty V := ⟨⟨(Classical.choice hW).val,f.le (Classical.choice hW).property⟩⟩
    apply X.germToFunctionField_injective W
    rw [localCoordinates_value,germToFunctionField_restrict,localCoordinates_value]
    change rationalValue X W ((rationalFunctions X).presheaf.map f.op s.val) /
      (C.generator i : X.functionField) = _
    exact congrArg (fun r : X.functionField =>
      r / (C.generator i : X.functionField))
      (rationalValue_restrict X f (show Γ(rationalFunctions X,V) from s.val))
  · have hbot : W=⊥ := by
      apply le_antisymm
      · intro x hx
        exact False.elim (hW ⟨⟨x,hx⟩⟩)
      · exact bot_le
    letI := regularSections_subsingleton_of_empty X W hbot
    exact Subsingleton.elim _ _

/-- A genuine local sheaf isomorphism, assembled from the natural local
coordinate maps on all smaller opens. -/
def localFrame (i : C.index) :
    C.sheaf.over (C.openSet i) ≅
      SheafOfModules.unit (X.ringCatSheaf.over (C.openSet i)) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk
      (fun V => (C.localCoordinates i V.unop.left V.unop.hom.le).toModuleIso)
      (by
        intro V W f
        ext s
        exact C.localCoordinates_restrict i f.unop.left
          V.unop.hom.le W.unop.hom.le s)

/-- The cocycle constructs an actual invertible fractional sheaf. -/
def toCartierData : CartierData X where
  sheaf := C.sheaf
  inclusion := C.inclusion
  inclusion_injective := C.inclusion_injective
  locallyFree := by
    intro x
    obtain ⟨i,hxi⟩ := C.covers x
    exact ⟨C.openSet i,hxi,⟨C.localFrame i⟩⟩

@[simp] theorem toCartierData_sectionValue (V : X.Opens) [Nonempty V]
    (s : Γ(C.toCartierData.sheaf,V)) :
    C.toCartierData.sectionValue V s = rationalValue X V s.val := rfl

end RationalCartierCocycle

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.mem_submodule_iff_local
#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.localCoordinatesNonempty
#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.toCartierData
end
end Source_ToricCartierCocycle
-- END ORIGINAL PaperVerification.ToricCartierCocycle


-- BEGIN ORIGINAL PaperVerification.ToricInvertibleAffine
section Source_ToricInvertibleAffine

-- original header: module

-- original header: public import PaperVerification.ToricCartierSheaf
-- original header: public import Mathlib.AlgebraicGeometry.Modules.Tilde
-- original header: public import Mathlib.CategoryTheory.Sites.Spaces

-- original header: @[expose] public section

/-!
# Actual rank-one sheaves and the affine tilde equivalence

The rank-one condition used for Cartier sheaves implies Mathlib's local-free
and quasi-coherent conditions. Thus the affine section module recovers the
actual sheaf through the existing tilde equivalence. The local statements
below retain actual principal opens and actual restriction maps.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

namespace PaperVerification.ToricSchemes

variable {X : Scheme.{u}} {M : X.Modules}

/-- The free sheaf on one generator is the actual structure module. -/
def freeSingletonIsoUnit (R : CategoryTheory.Sheaf
    (Opens.grothendieckTopology X) RingCat.{u}) :
    SheafOfModules.free (R := R) PUnit.{u+1} ≅ SheafOfModules.unit R :=
  coproductUniqueIso (fun _ : PUnit.{u+1} => SheafOfModules.unit R)

/-- A chosen rank-one neighborhood of each point. -/
def invertibleOpen (hM : IsInvertibleModule M) (x : X) : X.Opens :=
  (hM x).choose

theorem mem_invertibleOpen (hM : IsInvertibleModule M) (x : X) :
    x∈invertibleOpen hM x := (hM x).choose_spec.1

/-- The chosen local trivialization is an actual sheaf isomorphism. -/
def invertibleFrame (hM : IsInvertibleModule M) (x : X) :
    M.over (invertibleOpen hM x) ≅
      SheafOfModules.unit (X.ringCatSheaf.over (invertibleOpen hM x)) :=
  (hM x).choose_spec.2.some

/-- Evaluation of an actual local frame on a smaller open. -/
def invertibleFrameCoordinates (hM : IsInvertibleModule M) (x : X)
    (V : X.Opens) (hV : V ≤ invertibleOpen hM x) :
    Γ(M,V) ≃ₗ[Γ(X,V)] Γ(X,V) :=
  ((PresheafOfModules.evaluation
    (X.ringCatSheaf.over (invertibleOpen hM x)).obj
      (op (Over.mk (homOfLE hV)))).mapIso
    ((SheafOfModules.forget _).mapIso (invertibleFrame hM x))).toLinearEquiv

set_option backward.isDefEq.respectTransparency false in
/-- The chosen rank-one frame viewed as an isomorphism from a free sheaf. -/
def invertibleFreeFrame (hM : IsInvertibleModule M) (x : X) :
    SheafOfModules.free (R := X.ringCatSheaf.over (invertibleOpen hM x))
      PUnit.{u+1} ≅ (M : SheafOfModules.{u} X.ringCatSheaf).over (invertibleOpen hM x) :=
  coproductUniqueIso (fun _ : PUnit.{u+1} =>
    SheafOfModules.unit (X.ringCatSheaf.over (invertibleOpen hM x))) ≪≫
      (invertibleFrame hM x).symm

set_option backward.isDefEq.respectTransparency false in
/-- Actual local free generators, constructed from rank-one frames. -/
def invertibleLocalGenerators (hM : IsInvertibleModule M) :
    (M : SheafOfModules.{u} X.ringCatSheaf).LocalGeneratorsData where
  I := X
  X := invertibleOpen hM
  coversTop := by
    rw [Opens.coversTop_iff]
    apply le_antisymm le_top
    intro x hx
    exact Opens.mem_iSup.mpr ⟨x,mem_invertibleOpen hM x⟩
  generators x :=
    (SheafOfModules.GeneratingSections.equivOfIso (invertibleFreeFrame hM x))
      (SheafOfModules.free.generatingSections PUnit.{u+1})

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 2000000 in
instance invertibleLocalGenerators_isLocallyFree (hM : IsInvertibleModule M) :
    (invertibleLocalGenerators hM).IsLocallyFreeData where
  isIso x := by
    change X at x
    change IsIso
      (((SheafOfModules.free.generatingSections
        (R := X.ringCatSheaf.over (invertibleOpen hM x)) PUnit.{u+1}).ofEpi
          (invertibleFreeFrame hM x).hom).π)
    rw [SheafOfModules.GeneratingSections.ofEpi_π,
      SheafOfModules.free.generatingSections_π]
    exact IsIso.comp_isIso' (IsIso.id _) (invertibleFreeFrame hM x).isIso_hom

/-- Rank-one local triviality is genuine local freeness in Mathlib's sense. -/
theorem isLocallyFree_of_isInvertibleModule (hM : IsInvertibleModule M) :
    SheafOfModules.IsLocallyFree (R := X.ringCatSheaf)
      (M : SheafOfModules.{u} X.ringCatSheaf) :=
  (invertibleLocalGenerators hM).isLocallyFree

/-- In particular the actual invertible sheaf is quasi-coherent. -/
theorem isQuasicoherent_of_isInvertibleModule (hM : IsInvertibleModule M) :
    SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf)
      (M : SheafOfModules.{u} X.ringCatSheaf) := by
  exact (invertibleLocalGenerators hM).quasiCoherentData.isQuasicoherent

section Affine

variable {R : CommRingCat.{u}} (M : (Spec R).Modules)

set_option backward.isDefEq.respectTransparency.types false in
/-- The global section module of an invertible sheaf recovers the actual
sheaf, by the established quasi-coherent affine equivalence. -/
def invertibleAffineTildeIso (hM : IsInvertibleModule M) :
    tilde ((moduleSpecΓFunctor (R := R)).obj M) ≅ M := by
  exact @asIso (Spec R).Modules _ _ _ M.fromTildeΓ
    ((isQuasicoherent_iff_isIso_fromTildeΓ M).mp (isQuasicoherent_of_isInvertibleModule hM))

/-- The actual restriction map on a principal open is module localization. -/
theorem invertibleAffine_isLocalizing (hM : IsInvertibleModule M) :
    IsLocalizing (modulesSpecToSheaf.obj M) := by
  letI := isQuasicoherent_of_isInvertibleModule hM
  exact (isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance

/-- Each point has a principal neighborhood on which the actual sheaf is
trivial. No finite generation or affine correspondence is assumed. -/
theorem exists_basicOpen_frame (hM : IsInvertibleModule M)
    (x : Spec R) :
    ∃ f : R, x∈PrimeSpectrum.basicOpen f ∧
      PrimeSpectrum.basicOpen f ≤ invertibleOpen hM x := by
  obtain ⟨U,⟨_,⟨f,rfl⟩,rfl⟩,hx,hU⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open
      (mem_invertibleOpen hM x) (invertibleOpen hM x).isOpen
  exact ⟨f,hx,hU⟩

/-- A finite principal-open cover subordinate to the actual rank-one frames.
The cover is extracted from compactness of the affine spectrum. -/
theorem exists_finite_basicOpen_frames (hM : IsInvertibleModule M) :
    ∃ (ι : Type u) (_ : Fintype ι) (f : ι→R) (p : ι→Spec R),
      (⨆ i,PrimeSpectrum.basicOpen (f i))=⊤ ∧
      ∀ i,PrimeSpectrum.basicOpen (f i) ≤ invertibleOpen hM (p i) := by
  classical
  choose f hf hsub using exists_basicOpen_frame M hM
  have hcover : IsOpenCover (fun x : Spec R => PrimeSpectrum.basicOpen (f x)) := by
    apply le_antisymm le_top
    intro x hx
    exact Opens.mem_iSup.mpr ⟨x,hf x⟩
  obtain ⟨s,hs⟩ := hcover.exists_finite_of_compactSpace
  exact ⟨s,inferInstance,fun i=>f i.val,fun i=>i.val,hs,fun i=>hsub i.val⟩

end Affine

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.isQuasicoherent_of_isInvertibleModule
#print axioms PaperVerification.ToricSchemes.invertibleAffineTildeIso
#print axioms PaperVerification.ToricSchemes.exists_finite_basicOpen_frames
end
end Source_ToricInvertibleAffine
-- END ORIGINAL PaperVerification.ToricInvertibleAffine


-- BEGIN ORIGINAL PaperVerification.ToricCartierPresentation
section Source_ToricCartierPresentation

-- original header: module

-- original header: public import PaperVerification.ToricCartierCocycle
-- original header: public import PaperVerification.ToricInvertibleAffine

-- original header: @[expose] public section

/-!
# Equivalence of actual fractional sheaves and Cartier equations

An invertible fractional sheaf supplies rational local generators. Conversely,
the sheaf constructed from these generators recovers the original sheaf and
its actual embedding into rational functions. The proof uses the sheaf gluing
axiom, rather than assuming a section-space correspondence.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace PaperVerification.ToricSchemes

variable {X : Scheme.{u}} [IsIntegral X]

namespace CartierData

variable (D : CartierData X)

set_option backward.isDefEq.respectTransparency false in
/-- Local membership in the actual image of a fractional sheaf is sufficient
for membership on the whole open set. -/
theorem exists_section_of_locally_in_range (U : X.Opens) [Nonempty U]
    (r : X.functionField)
    (hlocal : ∀ x : U, ∃ V : X.Opens, V≤U ∧ x.val∈V ∧
      ∃ s : Γ(D.sheaf,V), ∀ hV : Nonempty V,
        @sectionValue X inferInstance D V hV s = r) :
    ∃ s : Γ(D.sheaf,U), D.sectionValue U s = r := by
  classical
  have hUne : Nonempty U := inferInstance
  choose V hVU hxV s hs using hlocal
  letI (x : U) : Nonempty (V x) := ⟨⟨x.val,hxV x⟩⟩
  have hcover : U≤⨆ x : U,V x := by
    intro x hx
    exact Opens.mem_iSup.mpr ⟨⟨x,hx⟩,hxV ⟨x,hx⟩⟩
  have hcompatible : D.sheaf.presheaf.IsCompatible V s := by
    intro x y
    letI : Nonempty (V x⊓V y : X.Opens) :=
      ⟨⟨genericPoint X,genericPoint_mem_open X (V x),
        genericPoint_mem_open X (V y)⟩⟩
    apply D.sectionValue_injective (V x⊓V y)
    rw [D.sectionValue_restrict,D.sectionValue_restrict]
    exact (hs x inferInstance).trans (hs y inferInstance).symm
  let F : TopCat.Sheaf AddCommGrpCat X := ⟨D.sheaf.presheaf,D.sheaf.isSheaf⟩
  obtain ⟨g,hg,-⟩ := F.existsUnique_gluing' V U
    (fun x=>homOfLE (hVU x)) hcover s hcompatible
  refine ⟨g,?_⟩
  let x : U := Classical.choice hUne
  calc
    D.sectionValue U g =
      D.sectionValue (V x) (D.sheaf.presheaf.map (homOfLE (hVU x)).op g) :=
        (D.sectionValue_restrict _ g).symm
    _ = D.sectionValue (V x) (s x) := congrArg _ (hg x)
    _ = r := hs x inferInstance

/-- The genuine Cartier equations derived from the chosen local frames. -/
def localCocycle : RationalCartierCocycle X where
  index := X
  openSet := invertibleOpen D.locallyFree
  covers x := ⟨x,mem_invertibleOpen D.locallyFree x⟩
  generator x := by
    letI : Nonempty (invertibleOpen D.locallyFree x) :=
      ⟨⟨x,mem_invertibleOpen D.locallyFree x⟩⟩
    exact Units.mk0
      (D.frameRationalGenerator (invertibleFrame D.locallyFree x))
      (D.frameRationalGenerator_ne_zero (invertibleFrame D.locallyFree x))
  transition i j x hxi hxj := by
    let U := invertibleOpen D.locallyFree i
    let W := invertibleOpen D.locallyFree j
    let V : X.Opens := U⊓W
    letI : Nonempty U := ⟨⟨i,mem_invertibleOpen D.locallyFree i⟩⟩
    letI : Nonempty W := ⟨⟨j,mem_invertibleOpen D.locallyFree j⟩⟩
    letI : Nonempty V := ⟨⟨x,hxi,hxj⟩⟩
    change D.frameRationalGenerator (invertibleFrame D.locallyFree i) /
      D.frameRationalGenerator (invertibleFrame D.locallyFree j) ∈
        regularAtSubring X x
    obtain ⟨a,ha⟩ := D.exists_frameTransitionUnit
      (invertibleFrame D.locallyFree i) (invertibleFrame D.locallyFree j)
      (V := V) inf_le_left inf_le_right
    rw [← ha]
    exact regular_germ_mem_regularAt X V (a : Γ(X,V)) x ⟨hxi,hxj⟩

@[simp] theorem localCocycle_openSet (x : X) :
    D.localCocycle.openSet x = invertibleOpen D.locallyFree x := rfl

@[simp] theorem localCocycle_generator (x : X)
    [Nonempty (invertibleOpen D.locallyFree x)] :
    (D.localCocycle.generator x : X.functionField) =
      D.frameRationalGenerator (invertibleFrame D.locallyFree x) := rfl

/-- Actual sections satisfy the local Cartier regularity condition. -/
theorem inclusion_isSection (U : X.Opens) (s : Γ(D.sheaf,U)) :
    D.localCocycle.IsSection U (D.inclusion.app U s) := by
  intro i x hxi
  let W := invertibleOpen D.locallyFree i
  let V : X.Opens := W⊓U
  letI : Nonempty U := ⟨x⟩
  letI : Nonempty W := ⟨⟨i,mem_invertibleOpen D.locallyFree i⟩⟩
  letI : Nonempty V := ⟨⟨x.val,hxi,x.property⟩⟩
  have hr : D.sectionValue U s ∈ D.sectionValueRange V :=
    ⟨D.sheaf.presheaf.map (homOfLE inf_le_right).op s,D.sectionValue_restrict _ s⟩
  obtain ⟨a,ha⟩ :=
    (D.mem_sectionValueRange_iff (invertibleFrame D.locallyFree i)
      (V := V) inf_le_left _).mp hr
  have ha' : X.germToFunctionField V a =
      D.sectionValue U s / D.frameRationalGenerator (invertibleFrame D.locallyFree i) :=
    (eq_div_iff (D.frameRationalGenerator_ne_zero _)).mpr ha
  simp only [rationalValueAt_eq,localCocycle_generator]
  change D.sectionValue U s / D.frameRationalGenerator (invertibleFrame D.locallyFree i) ∈
    regularAtSubring X x.val
  rw [← ha']
  exact regular_germ_mem_regularAt X V a x.val ⟨hxi,x.property⟩

/-- Every section obtained from the derived Cartier equations is an actual
section of the original fractional sheaf. -/
theorem exists_section_of_localCocycle (U : X.Opens) [Nonempty U]
    (s : Γ(rationalFunctions X,U)) (hs : D.localCocycle.IsSection U s) :
    ∃ t : Γ(D.sheaf,U), D.inclusion.app U t = s := by
  have hloc : ∀ x : U, ∃ V : X.Opens, V≤U ∧ x.val∈V ∧
      ∃ t : Γ(D.sheaf,V), ∀ hV : Nonempty V,
        @sectionValue X inferInstance D V hV t = rationalValue X U s := by
    intro x
    let W := invertibleOpen D.locallyFree x.val
    let V : X.Opens := W⊓U
    letI : Nonempty W := ⟨⟨x.val,mem_invertibleOpen D.locallyFree x.val⟩⟩
    have hxV : x.val∈V := ⟨mem_invertibleOpen D.locallyFree x.val,x.property⟩
    letI : Nonempty V := ⟨⟨x.val,hxV⟩⟩
    let q := D.frameRationalGenerator (invertibleFrame D.locallyFree x.val)
    have hregular : ∀ y∈V,
        rationalValue X U s/q ∈ regularAtSubring X y := by
      intro y hy
      simpa only [rationalValueAt_eq,localCocycle_generator] using
        hs x.val ⟨y,hy.2⟩ hy.1
    obtain ⟨a,ha⟩ := exists_regularSection_of_stalkwise X V
      (rationalValue X U s/q) hregular
    let t := a • D.frameGenerator (invertibleFrame D.locallyFree x.val) V inf_le_left
    refine ⟨V,inf_le_right,hxV,t,?_⟩
    intro hV
    change D.sectionValue V
      (a • D.frameGenerator (invertibleFrame D.locallyFree x.val) V inf_le_left) =
        rationalValue X U s
    rw [D.sectionValue_smul,D.sectionValue_frameGenerator,ha]
    exact div_mul_cancel₀ _ (D.frameRationalGenerator_ne_zero _)
  obtain ⟨t,ht⟩ := D.exists_section_of_locally_in_range U (rationalValue X U s) hloc
  refine ⟨t,(rationalValue X U).injective ?_⟩
  simpa only [sectionValue_apply] using ht

/-- Exact actual-image characterization on every nonempty open. -/
theorem localCocycle_isSection_iff (U : X.Opens) [Nonempty U]
    (s : Γ(rationalFunctions X,U)) :
    D.localCocycle.IsSection U s ↔
      ∃ t : Γ(D.sheaf,U),D.inclusion.app U t=s :=
  ⟨D.exists_section_of_localCocycle U s,
    by rintro ⟨t,rfl⟩; exact D.inclusion_isSection U t⟩

/-- The canonical map into the sheaf reconstructed from local generators. -/
def presentationMap (U : X.Opens) :
    Γ(D.sheaf,U) →ₗ[Γ(X,U)] Γ(D.localCocycle.sheaf,U) where
  toFun s := ⟨D.inclusion.app U s,D.inclusion_isSection U s⟩
  map_add' s t := Subtype.ext (map_add _ _ _)
  map_smul' a s := Subtype.ext (D.inclusion.app_smul a s)

theorem presentationMap_bijective (U : X.Opens) :
    Function.Bijective (D.presentationMap U) := by
  classical
  refine ⟨fun s t h=>D.inclusion_injective U (congrArg Subtype.val h),?_⟩
  intro s
  by_cases hU : Nonempty U
  · letI := hU
    obtain ⟨t,ht⟩ := D.exists_section_of_localCocycle U s.val s.property
    exact ⟨t,Subtype.ext ht⟩
  · have hbot : U=⊥ := by
      apply le_antisymm
      · intro x hx
        exact False.elim (hU ⟨⟨x,hx⟩⟩)
      · exact bot_le
    letI := regularSections_subsingleton_of_empty X U hbot
    letI := Module.subsingleton Γ(X,U) Γ(D.localCocycle.sheaf,U)
    exact ⟨0,Subsingleton.elim _ _⟩

def presentationLinearEquiv (U : X.Opens) :
    Γ(D.sheaf,U) ≃ₗ[Γ(X,U)] Γ(D.localCocycle.sheaf,U) :=
  LinearEquiv.ofBijective (D.presentationMap U) (D.presentationMap_bijective U)

/-- Recovery is an actual natural sheaf isomorphism. -/
def presentationIso : D.sheaf ≅ D.localCocycle.sheaf :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk
      (fun U=>(D.presentationLinearEquiv U.unop).toModuleIso)
      (by
        intro U V f
        ext s
        apply Subtype.ext
        exact PresheafOfModules.naturality_apply D.inclusion.val f s)

/-- The recovered isomorphism respects the actual rational embedding. -/
theorem equivalent_localCocycle : D.Equivalent D.localCocycle.toCartierData := by
  refine ⟨D.presentationIso,?_⟩
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  rfl

end CartierData

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.CartierData.localCocycle_isSection_iff
#print axioms PaperVerification.ToricSchemes.CartierData.presentationIso
#print axioms PaperVerification.ToricSchemes.CartierData.equivalent_localCocycle
end
end Source_ToricCartierPresentation
-- END ORIGINAL PaperVerification.ToricCartierPresentation


-- BEGIN ORIGINAL PaperVerification.ToricCartierProducts
section Source_ToricCartierProducts

-- original header: module

-- original header: public import PaperVerification.ToricCartierPresentation
-- original header: public import Mathlib.LinearAlgebra.TensorProduct.Basic

-- original header: @[expose] public section

/-!
# Cartier products and actual section multiplication

Products and inverses are defined by multiplying and inverting genuine local
rational generators on a common open refinement. The section multiplication
map is multiplication of actual rational functions, first as a bilinear map
of actual sheaf sections and then as the induced tensor-product map.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open scoped TensorProduct

namespace PaperVerification.ToricSchemes

variable {X : Scheme.{u}} [IsIntegral X]

/-- The pushforward rational-function sections carry the actual ring
structure of the generic-point structure sheaf on the inverse image. -/
instance rationalSectionsCommRing (U : X.Opens) : CommRing Γ(rationalFunctions X,U) :=
  inferInstanceAs (CommRing Γ(Spec X.functionField,genericPointMap X ⁻¹ᵁ U))

/-- Multiplication in the actual generic-point pushforward ring. -/
def rationalMul (U : X.Opens) (s t : Γ(rationalFunctions X,U)) :
    Γ(rationalFunctions X,U) :=
  (show Γ(Spec X.functionField,genericPointMap X ⁻¹ᵁ U) from s) *
    (show Γ(Spec X.functionField,genericPointMap X ⁻¹ᵁ U) from t)

@[simp] theorem rationalValue_mul (U : X.Opens) [Nonempty U]
    (s t : Γ(rationalFunctions X,U)) :
    rationalValue X U (rationalMul U s t) =
      rationalValue X U s * rationalValue X U t :=
  map_mul (rationalSectionValueIso X U).hom.hom
    (show Γ(Spec X.functionField,genericPointMap X ⁻¹ᵁ U) from s)
    (show Γ(Spec X.functionField,genericPointMap X ⁻¹ᵁ U) from t)

theorem rationalMul_add_left (U : X.Opens) (s t r : Γ(rationalFunctions X,U)) :
    rationalMul U (s+t) r = rationalMul U s r + rationalMul U t r := add_mul s t r

theorem rationalMul_add_right (U : X.Opens) (s t r : Γ(rationalFunctions X,U)) :
    rationalMul U s (t+r) = rationalMul U s t + rationalMul U s r := mul_add s t r

theorem rationalMul_smul_left (U : X.Opens) (a : Γ(X,U))
    (s t : Γ(rationalFunctions X,U)) :
    rationalMul U (a • s) t = a • rationalMul U s t := by
  change ((genericPointMap X).app U a *
      (show Γ(Spec X.functionField,genericPointMap X ⁻¹ᵁ U) from s)) *
      (show Γ(Spec X.functionField,genericPointMap X ⁻¹ᵁ U) from t) =
    (genericPointMap X).app U a *
      ((show Γ(Spec X.functionField,genericPointMap X ⁻¹ᵁ U) from s) *
        (show Γ(Spec X.functionField,genericPointMap X ⁻¹ᵁ U) from t))
  exact mul_assoc _ _ _

theorem rationalMul_smul_right (U : X.Opens) (a : Γ(X,U))
    (s t : Γ(rationalFunctions X,U)) :
    rationalMul U s (a • t) = a • rationalMul U s t := by
  change (show Γ(Spec X.functionField,genericPointMap X ⁻¹ᵁ U) from s) *
      ((genericPointMap X).app U a *
        (show Γ(Spec X.functionField,genericPointMap X ⁻¹ᵁ U) from t)) =
    (genericPointMap X).app U a *
      ((show Γ(Spec X.functionField,genericPointMap X ⁻¹ᵁ U) from s) *
        (show Γ(Spec X.functionField,genericPointMap X ⁻¹ᵁ U) from t))
  exact mul_left_comm _ _ _

theorem rationalMul_restrict {U V : X.Opens} (i : V ⟶ U)
    (s t : Γ(rationalFunctions X,U)) :
    (rationalFunctions X).presheaf.map i.op (rationalMul U s t) =
      rationalMul V ((rationalFunctions X).presheaf.map i.op s)
        ((rationalFunctions X).presheaf.map i.op t) :=
  map_mul ((Spec X.functionField).presheaf.map
    ((Opens.map (genericPointMap X).base).map i).op).hom
    (show Γ(Spec X.functionField,genericPointMap X ⁻¹ᵁ U) from s)
    (show Γ(Spec X.functionField,genericPointMap X ⁻¹ᵁ U) from t)

namespace RationalCartierCocycle

variable (C D : RationalCartierCocycle X)

/-- Addition of Cartier divisors multiplies their O(D) local generators. -/
def mul : RationalCartierCocycle X where
  index := C.index × D.index
  openSet i := C.openSet i.1 ⊓ D.openSet i.2
  covers x := by
    obtain ⟨i,hi⟩ := C.covers x
    obtain ⟨j,hj⟩ := D.covers x
    exact ⟨(i,j),hi,hj⟩
  generator i := C.generator i.1 * D.generator i.2
  transition i j x hi hj := by
    have hC := C.transition i.1 j.1 x hi.1 hj.1
    have hD := D.transition i.2 j.2 x hi.2 hj.2
    have h := (regularAtSubring X x).mul_mem hC hD
    simpa only [Units.val_mul,div_mul_div_comm] using h

/-- Negation of a Cartier divisor inverts its nonzero rational generators. -/
def inv : RationalCartierCocycle X where
  index := C.index
  openSet := C.openSet
  covers := C.covers
  generator i := (C.generator i)⁻¹
  transition i j x hi hj := by
    have h := C.transition j i x hj hi
    have he : ((C.generator i : X.functionField)⁻¹ /
        (C.generator j : X.functionField)⁻¹) =
        (C.generator j : X.functionField)/(C.generator i : X.functionField) := by
      field_simp [Units.ne_zero]
    simpa only [Units.val_inv_eq_inv_val,he] using h

/-- A principal fractional sheaf, with its specified rational generator. -/
def principal (q : X.functionFieldˣ) : RationalCartierCocycle X where
  index := PUnit.{u+1}
  openSet _ := ⊤
  covers x := ⟨PUnit.unit,trivial⟩
  generator _ := q
  transition _ _ _ _ _ := by simpa using (regularAtSubring X _).one_mem

theorem isSection_mul (U : X.Opens)
    (s t : Γ(rationalFunctions X,U))
    (hs : C.IsSection U s) (ht : D.IsSection U t) :
    (C.mul D).IsSection U (rationalMul U s t) := by
  intro i x hx
  letI : Nonempty U := ⟨x⟩
  have h := (regularAtSubring X x.val).mul_mem
    (hs i.1 x hx.1) (ht i.2 x hx.2)
  simpa only [rationalValueAt_eq,rationalValue_mul,mul,Units.val_mul,
    div_mul_div_comm] using h

/-- Multiplication of actual sections, before passing to the tensor product. -/
def sectionProduct (U : X.Opens) :
    Γ(C.sheaf,U) →ₗ[Γ(X,U)] Γ(D.sheaf,U) →ₗ[Γ(X,U)] Γ((C.mul D).sheaf,U) where
  toFun s :=
    { toFun := fun t=>⟨rationalMul U s.val t.val,
        C.isSection_mul D U s.val t.val s.property t.property⟩
      map_add' := fun t r=>Subtype.ext (rationalMul_add_right U s.val t.val r.val)
      map_smul' := fun a t=>Subtype.ext (rationalMul_smul_right U a s.val t.val) }
  map_add' s t := by
    ext r
    exact Subtype.ext (rationalMul_add_left U s.val t.val r.val)
  map_smul' a s := by
    ext t
    exact Subtype.ext (rationalMul_smul_left U a s.val t.val)

@[simp] theorem sectionProduct_value (U : X.Opens) [Nonempty U]
    (s : Γ(C.sheaf,U)) (t : Γ(D.sheaf,U)) :
    (C.mul D).toCartierData.sectionValue U (C.sectionProduct D U s t) =
      C.toCartierData.sectionValue U s * D.toCartierData.sectionValue U t :=
  rationalValue_mul U s.val t.val

/-- The genuine section multiplication map on tensor products. -/
def sectionMultiplication (U : X.Opens) :
    Γ(C.sheaf,U) ⊗[Γ(X,U)] Γ(D.sheaf,U) →ₗ[Γ(X,U)] Γ((C.mul D).sheaf,U) :=
  TensorProduct.lift (C.sectionProduct D U)

@[simp] theorem sectionMultiplication_tmul (U : X.Opens)
    (s : Γ(C.sheaf,U)) (t : Γ(D.sheaf,U)) :
    C.sectionMultiplication D U (s ⊗ₜ[Γ(X,U)] t) = C.sectionProduct D U s t := rfl

theorem sectionProduct_restrict {U V : X.Opens} (i : V ⟶ U)
    (s : Γ(C.sheaf,U)) (t : Γ(D.sheaf,U)) :
    (C.mul D).sheaf.presheaf.map i.op (C.sectionProduct D U s t) =
      C.sectionProduct D V (C.sheaf.presheaf.map i.op s)
        (D.sheaf.presheaf.map i.op t) := by
  apply Subtype.ext
  exact rationalMul_restrict i s.val t.val

end RationalCartierCocycle

namespace CartierData

variable (D E : CartierData X)

/-- Sum of fractional Cartier presentations, constructed from actual local
equations on the common refinement. -/
def add : CartierData X := (D.localCocycle.mul E.localCocycle).toCartierData

/-- Additive inverse, using inverse rational local generators. -/
def neg : CartierData X := D.localCocycle.inv.toCartierData

/-- Section multiplication for arbitrary actual Cartier presentations. -/
def sectionProduct (U : X.Opens) :
    Γ(D.sheaf,U) →ₗ[Γ(X,U)] Γ(E.sheaf,U) →ₗ[Γ(X,U)] Γ((D.add E).sheaf,U) :=
  ((D.localCocycle.sectionProduct E.localCocycle U).compl₂ (E.presentationMap U)).comp
    (D.presentationMap U)

/-- The tensor-product multiplication map is induced by actual rational
function multiplication. -/
def sectionMultiplication (U : X.Opens) :
    Γ(D.sheaf,U) ⊗[Γ(X,U)] Γ(E.sheaf,U) →ₗ[Γ(X,U)] Γ((D.add E).sheaf,U) :=
  TensorProduct.lift (D.sectionProduct E U)

@[simp] theorem sectionProduct_value (U : X.Opens) [Nonempty U]
    (s : Γ(D.sheaf,U)) (t : Γ(E.sheaf,U)) :
    (D.add E).sectionValue U (D.sectionProduct E U s t) =
      D.sectionValue U s * E.sectionValue U t :=
  rationalValue_mul U (D.inclusion.app U s) (E.inclusion.app U t)

@[simp] theorem sectionMultiplication_value_tmul (U : X.Opens) [Nonempty U]
    (s : Γ(D.sheaf,U)) (t : Γ(E.sheaf,U)) :
    (D.add E).sectionValue U (D.sectionMultiplication E U (s ⊗ₜ[Γ(X,U)] t)) =
      D.sectionValue U s * E.sectionValue U t :=
  D.sectionProduct_value E U s t

end CartierData

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.sectionProduct_restrict
#print axioms PaperVerification.ToricSchemes.CartierData.sectionMultiplication_value_tmul
end
end Source_ToricCartierProducts
-- END ORIGINAL PaperVerification.ToricCartierProducts


-- BEGIN ORIGINAL PaperVerification.ToricCartierBaseSections
section Source_ToricCartierBaseSections

-- original header: module

-- original header: public import PaperVerification.ToricCartierProducts
-- original header: public import Mathlib.AlgebraicGeometry.Over
-- original header: public import Mathlib.LinearAlgebra.TensorProduct.Tower

-- original header: @[expose] public section

/-!
# Actual base-field section multiplication

The scalar map comes from the given structural morphism X→Spec k, followed
by the actual structure-sheaf restriction. Consequently the multiplication
map here is the tensor map over the base field, without assuming Γ(X,O_X)=k.
The rational-value square is proved on pure tensors and hence on the whole
tensor product.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct

namespace PaperVerification.ToricSchemes

namespace BaseSections

variable (k : Type u) [CommRing k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))]

/-- The scalar map is induced by the actual structural morphism. -/
def scalarMap (U : X.Opens) : k →+* Γ(X,U) :=
  (X.presheaf.map (homOfLE le_top).op).hom.comp
    (((X ↘ Spec (CommRingCat.of k)).appTop).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)

scoped instance sectionsAlgebra (U : X.Opens) : Algebra k Γ(X,U) :=
  (scalarMap k X U).toAlgebra

scoped instance sectionsModule (M : X.Modules) (U : X.Opens) : Module k Γ(M,U) :=
  Module.compHom Γ(M,U) (scalarMap k X U)

scoped instance sectionsScalarTower (M : X.Modules) (U : X.Opens) :
    IsScalarTower k Γ(X,U) Γ(M,U) :=
  IsScalarTower.of_compHom k Γ(X,U) Γ(M,U)

variable [IsIntegral X]

scoped instance functionFieldAlgebra : Algebra k X.functionField :=
  ((X.germToFunctionField ⊤).hom.comp (scalarMap k X ⊤)).toAlgebra

scoped instance functionFieldScalarTower : IsScalarTower k Γ(X,⊤) X.functionField :=
  IsScalarTower.of_algebraMap_eq' rfl

end BaseSections

open scoped BaseSections

namespace CartierData

variable (k : Type u) [CommRing k] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of k))] (D E : CartierData X)

/-- Actual rational values of global sections as a base-linear map. -/
def globalSectionValue : Γ(D.sheaf,⊤) →ₗ[k] X.functionField :=
  (D.sectionValue ⊤).restrictScalars k

theorem globalSectionValue_injective : Function.Injective (D.globalSectionValue k) :=
  D.sectionValue_injective ⊤

/-- Multiplication of actual sections as a bilinear map over the base. -/
def sectionProductOver :
    Γ(D.sheaf,⊤) →ₗ[k] Γ(E.sheaf,⊤) →ₗ[k] Γ((D.add E).sheaf,⊤) :=
  (D.sectionProduct E ⊤).restrictScalars₁₂ k k

/-- The section multiplication map in the manuscript, with its tensor
product over the actual base field (indeed over any commutative base ring). -/
def sectionMultiplicationOver :
    Γ(D.sheaf,⊤) ⊗[k] Γ(E.sheaf,⊤) →ₗ[k] Γ((D.add E).sheaf,⊤) :=
  TensorProduct.lift (D.sectionProductOver k E)

@[simp] theorem sectionMultiplicationOver_value_tmul
    (s : Γ(D.sheaf,⊤)) (t : Γ(E.sheaf,⊤)) :
    (D.add E).globalSectionValue k (D.sectionMultiplicationOver k E (s ⊗ₜ[k] t)) =
      D.globalSectionValue k s * E.globalSectionValue k t :=
  D.sectionProduct_value E ⊤ s t

/-- The actual section tensor map becomes literal multiplication in K(X)
under the actual injective rational-value maps. -/
theorem globalSectionValue_comp_sectionMultiplicationOver :
    ((D.add E).globalSectionValue k).comp (D.sectionMultiplicationOver k E) =
      (LinearMap.mul' k X.functionField).comp
        (TensorProduct.map (D.globalSectionValue k) (E.globalSectionValue k)) := by
  apply TensorProduct.ext'
  intro s t
  exact D.sectionMultiplicationOver_value_tmul k E s t

/-- Surjectivity may be checked in the actual function field because the
target section map is proved injective. -/
theorem sectionMultiplicationOver_surjective_iff_range :
    Function.Surjective (D.sectionMultiplicationOver k E) ↔
      ((LinearMap.mul' k X.functionField).comp
        (TensorProduct.map (D.globalSectionValue k) (E.globalSectionValue k))).range =
      ((D.add E).globalSectionValue k).range := by
  rw [← D.globalSectionValue_comp_sectionMultiplicationOver k E]
  constructor
  · intro hs
    ext r
    constructor
    · rintro ⟨s,rfl⟩
      exact ⟨D.sectionMultiplicationOver k E s,rfl⟩
    · rintro ⟨t,rfl⟩
      obtain ⟨s,rfl⟩ := hs t
      exact ⟨s,rfl⟩
  · intro hr t
    have ht : (D.add E).globalSectionValue k t ∈
        (((D.add E).globalSectionValue k).comp
          (D.sectionMultiplicationOver k E)).range := by
      rw [hr]
      exact ⟨t,rfl⟩
    obtain ⟨s,hs⟩ := ht
    exact ⟨s,(D.add E).globalSectionValue_injective k hs⟩

end CartierData

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.CartierData.globalSectionValue_comp_sectionMultiplicationOver
#print axioms PaperVerification.ToricSchemes.CartierData.sectionMultiplicationOver_surjective_iff_range
end
end Source_ToricCartierBaseSections
-- END ORIGINAL PaperVerification.ToricCartierBaseSections


-- BEGIN ORIGINAL PaperVerification.ToricFunctionFieldBridge
section Source_ToricFunctionFieldBridge

-- original header: module

-- original header: public import PaperVerification.ToricRegularRational
-- original header: public import Mathlib.RingTheory.Localization.FractionRing

-- original header: @[expose] public section

/-!
# Restriction of actual rational functions to a dense open affine scheme

An open immersion between irreducible schemes identifies their generic
stalks.  The map below is the genuine stalk map of that immersion, with
the generic points identified by Mathlib's generic-point theorem.  Its
compatibility with regular sections is proved from stalk-map naturality.
For an affine source its target is identified with the ordinary fraction
field of the coordinate ring by the universal property of localization.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped nonZeroDivisors

variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    [IrreducibleSpace X] [IrreducibleSpace Y]

/-- Restriction to an open subscheme is an isomorphism of the actual
generic stalks.  No identification of rational functions is assumed. -/
def openImmersionFunctionFieldIso : Y.functionField ≅ X.functionField :=
  Y.presheaf.stalkCongr
      (.of_eq (genericPoint_eq_of_isOpenImmersion j).symm) ≪≫
    asIso (j.stalkMap (genericPoint X))

def openImmersionFunctionFieldEquiv : Y.functionField ≃+* X.functionField :=
  (openImmersionFunctionFieldIso j).commRingCatIsoToRingEquiv

/-- Every nonempty open of the target meets the open source.  This proves
the nonemptiness needed for its ordinary germ-to-function-field map. -/
theorem openImmersion_preimage_nonempty (U : Y.Opens) [Nonempty U] :
    Nonempty (j ⁻¹ᵁ U) := by
  refine ⟨⟨genericPoint X, ?_⟩⟩
  change j (genericPoint X) ∈ U
  rw [genericPoint_eq_of_isOpenImmersion j]
  exact ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr
    (by simpa using (show Nonempty U from inferInstance))

set_option backward.isDefEq.respectTransparency.types false in
/-- The generic-stalk isomorphism sends the germ of a regular section to
the germ of its actual sheaf restriction. -/
theorem openImmersionFunctionFieldIso_germ (U : Y.Opens) [Nonempty U]
    [Nonempty (j ⁻¹ᵁ U)] :
    Y.germToFunctionField U ≫ (openImmersionFunctionFieldIso j).hom =
      j.app U ≫ X.germToFunctionField (j ⁻¹ᵁ U) := by
  simp only [openImmersionFunctionFieldIso, Iso.trans_hom, Scheme.germToFunctionField,
    TopCat.Presheaf.stalkCongr_hom, asIso_hom, ← Category.assoc]
  rw [TopCat.Presheaf.germ_stalkSpecializes]
  exact j.germ_stalkMap U (genericPoint X) _

@[simp] theorem openImmersionFunctionFieldEquiv_germ (U : Y.Opens)
    [Nonempty U] [Nonempty (j ⁻¹ᵁ U)] (a : Γ(Y,U)) :
    openImmersionFunctionFieldEquiv j (Y.germToFunctionField U a) =
      X.germToFunctionField (j ⁻¹ᵁ U) (j.app U a) := by
  exact congrArg (fun f => f a) (openImmersionFunctionFieldIso_germ j U)

set_option backward.isDefEq.respectTransparency.types false in
/-- Compatibility with a composite of actual open immersions. -/
theorem openImmersionFunctionFieldIso_comp {Z : Scheme.{u}}
    [IrreducibleSpace Z] (g : Y ⟶ Z) [IsOpenImmersion g] :
    openImmersionFunctionFieldIso (j ≫ g) =
      openImmersionFunctionFieldIso g ≪≫ openImmersionFunctionFieldIso j := by
  apply Iso.ext
  apply Z.presheaf.stalk_hom_ext
  intro U hU
  letI : Nonempty U := ⟨⟨genericPoint Z,hU⟩⟩
  letI : Nonempty (g ⁻¹ᵁ U) := openImmersion_preimage_nonempty g U
  letI : Nonempty (j ⁻¹ᵁ (g ⁻¹ᵁ U)) :=
    openImmersion_preimage_nonempty j (g ⁻¹ᵁ U)
  letI : Nonempty ((j ≫ g) ⁻¹ᵁ U) := openImmersion_preimage_nonempty (j ≫ g) U
  change Z.germToFunctionField U ≫ (openImmersionFunctionFieldIso (j ≫ g)).hom =
    Z.germToFunctionField U ≫
      ((openImmersionFunctionFieldIso g).hom ≫ (openImmersionFunctionFieldIso j).hom)
  rw [openImmersionFunctionFieldIso_germ (j ≫ g) U, ← Category.assoc,
    openImmersionFunctionFieldIso_germ g U, Category.assoc,
    openImmersionFunctionFieldIso_germ j (g ⁻¹ᵁ U)]
  change (g.app U ≫ j.app (g ⁻¹ᵁ U)) ≫
      X.germToFunctionField (j ⁻¹ᵁ (g ⁻¹ᵁ U)) =
    g.app U ≫ (j.app (g ⁻¹ᵁ U) ≫ X.germToFunctionField (j ⁻¹ᵁ (g ⁻¹ᵁ U)))
  exact Category.assoc _ _ _

theorem openImmersionFunctionFieldEquiv_comp {Z : Scheme.{u}}
    [IrreducibleSpace Z] (g : Y ⟶ Z) [IsOpenImmersion g] :
    openImmersionFunctionFieldEquiv (j ≫ g) =
      (openImmersionFunctionFieldEquiv g).trans (openImmersionFunctionFieldEquiv j) := by
  ext r
  exact congrArg (fun e => e.hom r) (openImmersionFunctionFieldIso_comp j g)

/-- A regular function on a genuine nonempty chart open determines a
rational function on the ambient scheme, via the inverse generic-stalk
isomorphism. -/
def openImmersionRegularToFunctionField (U : X.Opens) [Nonempty U] :
    Γ(X,U) →+* Y.functionField :=
  (openImmersionFunctionFieldEquiv j).symm.toRingHom.comp
    (X.germToFunctionField U).hom

abbrev openImmersionGlobalToFunctionField : Γ(X,⊤) →+* Y.functionField :=
  openImmersionRegularToFunctionField j ⊤

theorem openImmersionRegularToFunctionField_injective [IsIntegral X]
    (U : X.Opens) [Nonempty U] :
    Function.Injective (openImmersionRegularToFunctionField j U) :=
  (openImmersionFunctionFieldEquiv j).symm.injective.comp
    (X.germToFunctionField_injective U)

theorem openImmersionGlobalToFunctionField_injective [IsIntegral X] :
    Function.Injective (openImmersionGlobalToFunctionField j) :=
  openImmersionRegularToFunctionField_injective j ⊤

/-- Changing to a smaller open chart leaves its rational value unchanged. -/
theorem openImmersionGlobalToFunctionField_restrict {Z : Scheme.{u}}
    [IrreducibleSpace Z] (g : Y ⟶ Z) [IsOpenImmersion g] (a : Γ(Y,⊤)) :
    openImmersionGlobalToFunctionField (j ≫ g) (j.appTop a) =
      openImmersionGlobalToFunctionField g a := by
  apply (openImmersionFunctionFieldEquiv (j ≫ g)).injective
  change (openImmersionFunctionFieldEquiv (j ≫ g))
      ((openImmersionFunctionFieldEquiv (j ≫ g)).symm
        (X.germToFunctionField ⊤ (j.appTop a))) =
    (openImmersionFunctionFieldEquiv (j ≫ g))
      ((openImmersionFunctionFieldEquiv g).symm (Y.germToFunctionField ⊤ a))
  rw [RingEquiv.apply_symm_apply, openImmersionFunctionFieldEquiv_comp]
  simp only [RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
  letI : Nonempty (j ⁻¹ᵁ (⊤ : Y.Opens)) := openImmersion_preimage_nonempty j ⊤
  exact (openImmersionFunctionFieldEquiv_germ j ⊤ a).symm

theorem openImmersionRegularToFunctionField_restrict
    {U V : X.Opens} [Nonempty U] [Nonempty V] (i : V ⟶ U) (a : Γ(X,U)) :
    openImmersionRegularToFunctionField j V (X.presheaf.map i.op a) =
      openImmersionRegularToFunctionField j U a := by
  change (openImmersionFunctionFieldEquiv j).symm
      (X.germToFunctionField V (X.presheaf.map i.op a)) =
    (openImmersionFunctionFieldEquiv j).symm (X.germToFunctionField U a)
  exact congrArg (openImmersionFunctionFieldEquiv j).symm
    (X.presheaf.germ_res_apply i (genericPoint X) _ a)

theorem openImmersion_image_nonempty (U : X.Opens) [Nonempty U] :
    Nonempty (j ''ᵁ U) := by
  let x : U := Classical.choice (show Nonempty U from inferInstance)
  exact ⟨⟨j x,⟨x.val,x.property,rfl⟩⟩⟩

/-- The inverse field map of a chart section agrees with its ordinary
regular section on the open image, under the open-immersion section iso. -/
theorem openImmersionRegularToFunctionField_eq_germ_image
    (U : X.Opens) [Nonempty U] [Nonempty (j ''ᵁ U)] (a : Γ(X,U)) :
    openImmersionRegularToFunctionField j U a =
      Y.germToFunctionField (j ''ᵁ U) ((j.appIso U).inv a) := by
  letI : Nonempty (j ⁻¹ᵁ (j ''ᵁ U)) :=
    openImmersion_preimage_nonempty j (j ''ᵁ U)
  apply (openImmersionFunctionFieldEquiv j).injective
  change (openImmersionFunctionFieldEquiv j)
      ((openImmersionFunctionFieldEquiv j).symm (X.germToFunctionField U a)) =
    openImmersionFunctionFieldEquiv j
      (Y.germToFunctionField (j ''ᵁ U) ((j.appIso U).inv a))
  rw [RingEquiv.apply_symm_apply, openImmersionFunctionFieldEquiv_germ]
  have h := congrArg (fun f => f a) (j.appIso_inv_app U)
  simp only [ConcreteCategory.comp_apply] at h
  change X.germToFunctionField U a =
    X.germToFunctionField (j ⁻¹ᵁ (j ''ᵁ U))
      (j.app (j ''ᵁ U) ((j.appIso U).inv a))
  rw [h]
  exact (X.presheaf.germ_res_apply
    (eqToHom (Scheme.Hom.preimage_image_eq j U))
    (genericPoint X) (((genericPoint_spec X).mem_open_set_iff
      (j ⁻¹ᵁ (j ''ᵁ U)).isOpen).mpr
        (by simpa using (show Nonempty (j ⁻¹ᵁ (j ''ᵁ U)) from inferInstance))) a).symm

/-- A chart-regular function is regular in the ambient local ring at
every point of that chart.  Both local rings and their field embeddings
are the actual scheme stalk constructions. -/
theorem openImmersionRegularToFunctionField_mem_regularAt
    [IsIntegral Y] (U : X.Opens) [Nonempty U] (a : Γ(X,U))
    (x : X) (hx : x∈U) :
    openImmersionRegularToFunctionField j U a ∈ regularAtSubring Y (j x) := by
  letI : Nonempty (j ''ᵁ U) := openImmersion_image_nonempty j U
  rw [openImmersionRegularToFunctionField_eq_germ_image]
  exact regular_germ_mem_regularAt Y (j ''ᵁ U) ((j.appIso U).inv a)
    (j x) ⟨x,hx,rfl⟩

theorem openImmersionGlobalToFunctionField_mem_regularAt
    [IsIntegral Y] (a : Γ(X,⊤)) (x : X) :
    openImmersionGlobalToFunctionField j a ∈ regularAtSubring Y (j x) :=
  openImmersionRegularToFunctionField_mem_regularAt j ⊤ a x trivial

variable (R : CommRingCat.{u}) [IsDomain R]

/-- The actual generic stalk of `Spec R` is its fraction field, by the
uniqueness of localization at the nonzero divisors. -/
def affineFunctionFieldEquiv : (Spec R).functionField ≃ₐ[R] FractionRing R :=
  IsLocalization.algEquiv R⁰ (Spec R).functionField (FractionRing R)

@[simp] theorem affineFunctionFieldEquiv_algebraMap (r : R) :
    affineFunctionFieldEquiv R (algebraMap R (Spec R).functionField r) =
      algebraMap R (FractionRing R) r :=
  (affineFunctionFieldEquiv R).commutes r

/-- The algebra map used for this localization is precisely the germ of
the corresponding global regular function, not an unrelated embedding. -/
theorem affine_germToFunctionField_top :
    (Spec R).germToFunctionField ⊤ =
      (Scheme.ΓSpecIso R).hom ≫
        CommRingCat.ofHom (algebraMap R (Spec R).functionField) := by
  calc
    (Spec R).germToFunctionField ⊤ =
        (Scheme.ΓSpecIso R).hom ≫ ((Scheme.ΓSpecIso R).inv ≫
          (Spec R).germToFunctionField ⊤) := by simp
    _ = _ := rfl

@[simp] theorem affineFunctionFieldEquiv_germ_top (a : Γ(Spec R,⊤)) :
    affineFunctionFieldEquiv R ((Spec R).germToFunctionField ⊤ a) =
      algebraMap R (FractionRing R) ((Scheme.ΓSpecIso R).hom a) := by
  rw [affine_germToFunctionField_top]
  exact (affineFunctionFieldEquiv R).commutes _

/-- The function field of an irreducible scheme with this actual open
affine chart is the fraction field of its actual coordinate ring. -/
def affineOpenFunctionFieldEquiv (j : Spec R ⟶ Y) [IsOpenImmersion j] :
    Y.functionField ≃+* FractionRing R :=
  (openImmersionFunctionFieldEquiv j).trans
    (affineFunctionFieldEquiv R).toRingEquiv

@[simp] theorem affineOpenFunctionFieldEquiv_germ_top
    (j : Spec R ⟶ Y) [IsOpenImmersion j] (a : Γ(Y,⊤)) :
    affineOpenFunctionFieldEquiv R j (Y.germToFunctionField ⊤ a) =
      algebraMap R (FractionRing R) ((Scheme.ΓSpecIso R).hom (j.appTop a)) := by
  change affineFunctionFieldEquiv R
    (openImmersionFunctionFieldEquiv j (Y.germToFunctionField ⊤ a)) = _
  letI : Nonempty (j ⁻¹ᵁ (⊤ : Y.Opens)) := openImmersion_preimage_nonempty j ⊤
  rw [openImmersionFunctionFieldEquiv_germ]
  exact affineFunctionFieldEquiv_germ_top R (j.appTop a)

/-- Surjectivity is part of the constructed ring equivalence; in
particular every fraction arises from an actual rational function. -/
theorem affineOpenFunctionFieldEquiv_surjective
    (j : Spec R ⟶ Y) [IsOpenImmersion j] :
    Function.Surjective (affineOpenFunctionFieldEquiv R j) :=
  (affineOpenFunctionFieldEquiv R j).surjective

/-- The actual coordinate-ring embedding of an open affine chart into
the ambient function field, through regular sections and generic germs. -/
def affineOpenCoordinateMap (j : Spec R ⟶ Y) [IsOpenImmersion j] :
    R →+* Y.functionField :=
  (openImmersionGlobalToFunctionField j).comp (Scheme.ΓSpecIso R).inv.hom

def affineOpenCoordinateAlgebra (j : Spec R ⟶ Y) [IsOpenImmersion j] :
    Algebra R Y.functionField :=
  (affineOpenCoordinateMap R j).toAlgebra

@[simp] theorem affineOpenFunctionFieldEquiv_coordinateMap
    (j : Spec R ⟶ Y) [IsOpenImmersion j] (r : R) :
    affineOpenFunctionFieldEquiv R j (affineOpenCoordinateMap R j r) =
      algebraMap R (FractionRing R) r := by
  change affineFunctionFieldEquiv R
      ((openImmersionFunctionFieldEquiv j)
        ((openImmersionFunctionFieldEquiv j).symm
          ((Spec R).germToFunctionField ⊤ ((Scheme.ΓSpecIso R).inv r)))) = _
  rw [RingEquiv.apply_symm_apply, affineFunctionFieldEquiv_germ_top]
  simp

/-- The function-field equivalence respects the actual chart coordinate
map, hence is an algebra equivalence for that explicit algebra structure. -/
def affineOpenFunctionFieldAlgEquiv (j : Spec R ⟶ Y) [IsOpenImmersion j] :
    letI := affineOpenCoordinateAlgebra R j
    Y.functionField ≃ₐ[R] FractionRing R := by
  letI := affineOpenCoordinateAlgebra R j
  exact
    { affineOpenFunctionFieldEquiv R j with
      commutes' := affineOpenFunctionFieldEquiv_coordinateMap R j }

/-- The ambient function field is a fraction ring of an actual affine
chart, with precisely the regular-section/generic-stalk coordinate map.
This explicit structure can be used directly in Kähler localization. -/
theorem affineOpenCoordinate_isFractionRing
    (j : Spec R ⟶ Y) [IsOpenImmersion j] :
    letI := affineOpenCoordinateAlgebra R j
    IsFractionRing R Y.functionField := by
  letI := affineOpenCoordinateAlgebra R j
  exact IsLocalization.isLocalization_of_algEquiv R⁰
    (affineOpenFunctionFieldAlgEquiv R j).symm

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.openImmersionFunctionFieldIso
#print axioms PaperVerification.ToricSchemes.openImmersionFunctionFieldIso_germ
#print axioms PaperVerification.ToricSchemes.affineOpenFunctionFieldEquiv
end
end Source_ToricFunctionFieldBridge
-- END ORIGINAL PaperVerification.ToricFunctionFieldBridge


-- BEGIN ORIGINAL PaperVerification.ToricDominantFunctionField
section Source_ToricDominantFunctionField

-- original header: module

-- original header: public import PaperVerification.ToricFunctionFieldBridge
-- original header: public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

-- original header: @[expose] public section

/-! # Actual function-field pullback along a dominant morphism -/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory TopologicalSpace

/-- A nonempty actual open subscheme of a preirreducible scheme is
dominant. This is a topological consequence of the open immersion, not
an additional density assumption on a chart. -/
instance (priority := 80) openImmersion_isDominant_of_preirreducible
    {U X : Scheme.{u}} [Nonempty U] [PreirreducibleSpace X]
    (j : U ⟶ X) [IsOpenImmersion j] : IsDominant j :=
  ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace j
    j.isOpenEmbedding.isOpenMap⟩

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsDominant f]
    [IrreducibleSpace X] [IrreducibleSpace Y]

theorem genericPoint_eq_of_isDominant :
    f (genericPoint X)=genericPoint Y := by
  apply ((genericPoint_spec Y).eq _).symm
  simpa only [Set.image_univ,f.denseRange.closure_range] using
    (genericPoint_spec X).image f.continuous

/-- This is the genuine map on generic stalks, with generic points
identified by dominance. No fraction-field embedding is postulated. -/
def dominantFunctionFieldMap : Y.functionField →+* X.functionField :=
  ((Y.presheaf.stalkCongr
      (.of_eq (genericPoint_eq_of_isDominant f).symm)).hom ≫
    f.stalkMap (genericPoint X)).hom

theorem dominant_preimage_nonempty (U : Y.Opens) [Nonempty U] :
    Nonempty (f ⁻¹ᵁ U) := by
  refine ⟨⟨genericPoint X,?_⟩⟩
  change f (genericPoint X)∈U
  rw [genericPoint_eq_of_isDominant]
  exact ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr
    (by simpa using (show Nonempty U from inferInstance))

set_option backward.isDefEq.respectTransparency.types false in
theorem dominantFunctionFieldMap_germ_hom (U : Y.Opens) [Nonempty U]
    [Nonempty (f ⁻¹ᵁ U)] :
    Y.germToFunctionField U ≫ CommRingCat.ofHom (dominantFunctionFieldMap f) =
      f.app U ≫ X.germToFunctionField (f ⁻¹ᵁ U) := by
  change Y.germToFunctionField U ≫
    ((Y.presheaf.stalkCongr
      (.of_eq (genericPoint_eq_of_isDominant f).symm)).hom ≫
      f.stalkMap (genericPoint X)) = _
  simp only [Scheme.germToFunctionField,TopCat.Presheaf.stalkCongr_hom,
    ← Category.assoc]
  rw [TopCat.Presheaf.germ_stalkSpecializes]
  exact f.germ_stalkMap U (genericPoint X) _

@[simp] theorem dominantFunctionFieldMap_germ (U : Y.Opens) [Nonempty U]
    [Nonempty (f ⁻¹ᵁ U)] (a : Γ(Y,U)) :
    dominantFunctionFieldMap f (Y.germToFunctionField U a) =
      X.germToFunctionField (f ⁻¹ᵁ U) (f.app U a) :=
  congrArg (fun g=>g a) (dominantFunctionFieldMap_germ_hom f U)

set_option backward.isDefEq.respectTransparency.types false in
theorem dominantFunctionFieldMap_comp {Z : Scheme.{u}} [IrreducibleSpace Z]
    (g : Y ⟶ Z) [IsDominant g] :
    dominantFunctionFieldMap (f ≫ g) =
      (dominantFunctionFieldMap f).comp (dominantFunctionFieldMap g) := by
  apply CommRingCat.hom_ext_iff.mp
  apply Z.presheaf.stalk_hom_ext
  intro U hU
  letI : Nonempty U := ⟨⟨genericPoint Z,hU⟩⟩
  letI : Nonempty (g ⁻¹ᵁ U) := dominant_preimage_nonempty g U
  letI : Nonempty (f ⁻¹ᵁ (g ⁻¹ᵁ U)) :=
    dominant_preimage_nonempty f (g ⁻¹ᵁ U)
  letI : Nonempty ((f ≫ g) ⁻¹ᵁ U) := dominant_preimage_nonempty (f ≫ g) U
  change Z.germToFunctionField U ≫ CommRingCat.ofHom (dominantFunctionFieldMap (f≫g)) =
    Z.germToFunctionField U ≫
      (CommRingCat.ofHom (dominantFunctionFieldMap g) ≫
        CommRingCat.ofHom (dominantFunctionFieldMap f))
  calc
    _ = (g.app U ≫ f.app (g ⁻¹ᵁ U)) ≫
        X.germToFunctionField (f ⁻¹ᵁ (g ⁻¹ᵁ U)) :=
      dominantFunctionFieldMap_germ_hom (f ≫ g) U
    _ = g.app U ≫ (f.app (g ⁻¹ᵁ U) ≫
        X.germToFunctionField (f ⁻¹ᵁ (g ⁻¹ᵁ U))) := Category.assoc _ _ _
    _ = g.app U ≫ (Y.germToFunctionField (g ⁻¹ᵁ U) ≫
        CommRingCat.ofHom (dominantFunctionFieldMap f)) :=
      congrArg (fun h : Γ(Y,g ⁻¹ᵁ U) ⟶ X.functionField => g.app U ≫ h)
        (dominantFunctionFieldMap_germ_hom f (g ⁻¹ᵁ U)).symm
    _ = (g.app U ≫ Y.germToFunctionField (g ⁻¹ᵁ U)) ≫
        CommRingCat.ofHom (dominantFunctionFieldMap f) := (Category.assoc _ _ _).symm
    _ = (Z.germToFunctionField U ≫ CommRingCat.ofHom (dominantFunctionFieldMap g)) ≫
        CommRingCat.ofHom (dominantFunctionFieldMap f) :=
      congrArg (fun h : Γ(Z,U) ⟶ Y.functionField =>
        h ≫ CommRingCat.ofHom (dominantFunctionFieldMap f))
        (dominantFunctionFieldMap_germ_hom g U).symm
    _ = _ := Category.assoc _ _ _

theorem dominantFunctionFieldMap_injective [IsIntegral X] [IsIntegral Y] :
    Function.Injective (dominantFunctionFieldMap f) :=
  (dominantFunctionFieldMap f).injective

theorem dominantFunctionFieldMap_eq_openImmersion [IsOpenImmersion f] :
    dominantFunctionFieldMap f=(openImmersionFunctionFieldEquiv f).toRingHom := rfl

/-- Compatibility with every actual local ring, not just global regular
functions. This is the basic regularity input for Cartier pullback. -/
theorem dominantFunctionFieldMap_stalk [IsIntegral X] [IsIntegral Y]
    (x : X) (a : Y.presheaf.stalk (f x)) :
    dominantFunctionFieldMap f
        (algebraMap (Y.presheaf.stalk (f x)) Y.functionField a) =
      algebraMap (X.presheaf.stalk x) X.functionField (f.stalkMap x a) := by
  obtain ⟨U,hx,s,rfl⟩ := Y.presheaf.exists_germ_eq a
  letI : Nonempty U := ⟨⟨f x,hx⟩⟩
  letI : Nonempty (f ⁻¹ᵁ U) := ⟨⟨x,hx⟩⟩
  rw [Y.algebraMap_germ_eq_germToFunctionField hx s,
    dominantFunctionFieldMap_germ,f.germ_stalkMap_apply,
    X.algebraMap_germ_eq_germToFunctionField hx (f.app U s)]

theorem dominantFunctionFieldMap_mem_regularAt [IsIntegral X] [IsIntegral Y]
    (x : X) (a : Y.functionField) (ha : a∈regularAtSubring Y (f x)) :
    dominantFunctionFieldMap f a∈regularAtSubring X x := by
  obtain ⟨s,rfl⟩ := ha
  exact ⟨f.stalkMap x s,(dominantFunctionFieldMap_stalk f x s).symm⟩

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.dominantFunctionFieldMap_stalk
end
end Source_ToricDominantFunctionField
-- END ORIGINAL PaperVerification.ToricDominantFunctionField


-- BEGIN ORIGINAL PaperVerification.ToricBaseSectionNaturality
section Source_ToricBaseSectionNaturality

-- original header: module

-- original header: public import PaperVerification.ToricCartierBaseSections
-- original header: public import PaperVerification.ToricDominantFunctionField
-- original header: public import Mathlib.AlgebraicGeometry.Group.Affine

-- original header: @[expose] public section

/-! # Base scalars in actual regular and rational sections -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite

namespace PaperVerification.ToricSchemes.BaseSections

variable (k : Type u) [CommRing k]

theorem scalarMap_top_natural {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k))] (c : k) :
    f.appTop (scalarMap k Y ⊤ c)=scalarMap k X ⊤ c := by
  have h := congrArg
    (fun g : X ⟶ Spec (CommRingCat.of k)=>g.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c))
    (comp_over f (Spec (CommRingCat.of k)))
  simpa only [scalarMap,RingHom.comp_apply,homOfLE_refl,op_id,
    X.presheaf.map_id (op (⊤ : X.Opens)),Y.presheaf.map_id (op (⊤ : Y.Opens)),
    CommRingCat.hom_id,RingHom.id_apply,Scheme.Hom.comp_appTop,
    ConcreteCategory.comp_apply] using h

theorem scalarMap_affine_top (A : Type u) [CommRing A] [Algebra k A] (c : k) :
    scalarMap k (Spec (CommRingCat.of A)) ⊤ c =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv (algebraMap k A c) := by
  have h := congrArg
    (fun f : CommRingCat.of k ⟶ Γ(Spec (CommRingCat.of A),⊤) => f.hom c)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k A)))
  simpa only [scalarMap,RingHom.comp_apply,homOfLE_refl,op_id,
    (Spec (CommRingCat.of A)).presheaf.map_id (op (⊤ : (Spec (CommRingCat.of A)).Opens)),
    CommRingCat.hom_id,RingHom.id_apply,specOverSpec_over,
    CommRingCat.hom_comp,CommRingCat.hom_ofHom] using h.symm

theorem scalarMap_restrict {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] {U V : X.Opens} (h : V≤U) (c : k) :
    X.presheaf.map (homOfLE h).op (scalarMap k X U c)=scalarMap k X V c := by
  simp only [scalarMap,RingHom.comp_apply]
  exact congrArg (fun f=>f (((X ↘ Spec (CommRingCat.of k)).appTop).hom
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)))
      (X.presheaf.map_comp (homOfLE le_top).op (homOfLE h).op).symm

open scoped BaseSections

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]

theorem germ_scalarMap (U : X.Opens) [Nonempty U] (c : k) :
    X.germToFunctionField U (scalarMap k X U c)=algebraMap k X.functionField c := by
  have h := scalarMap_restrict k (X:=X) (U:=⊤) (V:=U) le_top c
  rw [← h,germToFunctionField_restrict]
  rfl

/-- The scalar-compatible regular-function embedding in the actual
generic stalk, on every nonempty open. -/
def regularValueAlgHom (U : X.Opens) [Nonempty U] :
    Γ(X,U) →ₐ[k] X.functionField where
  __ := (X.germToFunctionField U).hom
  commutes' := germ_scalarMap k U

/-- Dominant pullback preserves the scalars from the actual structure
morphisms. -/
def dominantFunctionFieldAlgHom (f : X ⟶ Y) [IsDominant f]
    [f.IsOver (Spec (CommRingCat.of k))] : Y.functionField →ₐ[k] X.functionField where
  __ := dominantFunctionFieldMap f
  commutes' c := by
    letI : Nonempty (f ⁻¹ᵁ (⊤ : Y.Opens)) := dominant_preimage_nonempty f ⊤
    change dominantFunctionFieldMap f
      (Y.germToFunctionField ⊤ (scalarMap k Y ⊤ c)) = _
    rw [dominantFunctionFieldMap_germ]
    change X.germToFunctionField ⊤ (f.appTop (scalarMap k Y ⊤ c)) = _
    rw [scalarMap_top_natural]
    rfl

end PaperVerification.ToricSchemes.BaseSections
end
end Source_ToricBaseSectionNaturality
-- END ORIGINAL PaperVerification.ToricBaseSectionNaturality


-- BEGIN ORIGINAL PaperVerification.ToricModuleFrameGluing
section Source_ToricModuleFrameGluing

-- original header: module

-- original header: public import PaperVerification.ToricCartierSheaf
-- original header: public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

-- original header: @[expose] public section

/-!
# Morphisms of genuine rank-one sheaves from compatible local frame images

This is a sheaf-theoretic gluing lemma. The source and target are actual
module sheaves, and every compatibility assertion uses their actual
restriction maps. It is independent of rational functions or dominance.
-/

noncomputable section

universe u v

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace PaperVerification.ToricSchemes

variable {X : Scheme.{u}}

abbrev moduleRes (M : X.Modules) {U V : X.Opens} (h : V≤U)
    (s : Γ(M,U)) : Γ(M,V) := M.presheaf.map (homOfLE h).op s

abbrev regularRes {U V : X.Opens} (h : V≤U) (a : Γ(X,U)) : Γ(X,V) :=
  X.presheaf.map (homOfLE h).op a

@[simp] theorem moduleRes_trans (M : X.Modules) {U V W : X.Opens}
    (hUV : V≤U) (hVW : W≤V) (s : Γ(M,U)) :
    moduleRes M hVW (moduleRes M hUV s) = moduleRes M (hVW.trans hUV) s := by
  simp only [moduleRes,← ConcreteCategory.comp_apply,← Functor.map_comp]
  rfl

@[simp] theorem moduleRes_smul (M : X.Modules) {U V : X.Opens}
    (h : V≤U) (a : Γ(X,U)) (s : Γ(M,U)) :
    moduleRes M h (a • s) = regularRes h a • moduleRes M h s :=
  M.map_smul (homOfLE h) a s

abbrev ModuleFrame (M : X.Modules) (U : X.Opens) :=
  M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)

namespace ModuleFrame

variable {M : X.Modules} {U : X.Opens} (e : ModuleFrame M U)

def coordinates (V : X.Opens) (hV : V≤U) : Γ(M,V) ≃ₗ[Γ(X,V)] Γ(X,V) :=
  ((PresheafOfModules.evaluation (X.ringCatSheaf.over U).obj
    (op (Over.mk (homOfLE hV)))).mapIso
      ((SheafOfModules.forget _).mapIso e)).toLinearEquiv

def generator (V : X.Opens) (hV : V≤U) : Γ(M,V) :=
  (e.coordinates V hV).symm 1

@[simp] theorem coordinates_generator (V : X.Opens) (hV : V≤U) :
    e.coordinates V hV (e.generator V hV)=1 :=
  (e.coordinates V hV).apply_symm_apply 1

theorem section_eq (V : X.Opens) (hV : V≤U) (s : Γ(M,V)) :
    s = e.coordinates V hV s • e.generator V hV := by
  apply (e.coordinates V hV).injective
  simp only [map_smul,coordinates_generator,smul_eq_mul,mul_one]

theorem coordinates_res {V W : X.Opens} (hV : V≤U) (hWV : W≤V)
    (s : Γ(M,V)) :
    e.coordinates W (hWV.trans hV) (moduleRes M hWV s) =
      regularRes hWV (e.coordinates V hV s) := by
  let a : Over.mk (homOfLE (hWV.trans hV)) ⟶ Over.mk (homOfLE hV) :=
    Over.homMk (homOfLE hWV) (by subsingleton)
  exact PresheafOfModules.naturality_apply e.hom.val a.op s

@[simp] theorem generator_res {V W : X.Opens} (hV : V≤U) (hWV : W≤V) :
    moduleRes M hWV (e.generator V hV)=e.generator W (hWV.trans hV) := by
  apply (e.coordinates W (hWV.trans hV)).injective
  rw [e.coordinates_res hV hWV,coordinates_generator,coordinates_generator]
  simp only [regularRes,map_one]

theorem coordinates_change {V W : X.Opens} (d : ModuleFrame M V)
    (hWU : W≤U) (hWV : W≤V) (s : Γ(M,W)) :
    d.coordinates W hWV s = e.coordinates W hWU s *
      d.coordinates W hWV (e.generator W hWU) := by
  conv_lhs => rw [e.section_eq W hWU s]
  rw [map_smul,smul_eq_mul]

end ModuleFrame

/-- Sections of a sheaf are determined by their restrictions to any
actual open cover, also after intersecting the cover with a smaller open. -/
theorem module_sections_ext_cover (M : X.Modules) {ι : Type v}
    (U : ι→X.Opens) (hcover : ∀ x : X,∃ i,x∈U i)
    (W : X.Opens) (s t : Γ(M,W))
    (h : ∀ i,moduleRes M (show W⊓U i≤W from inf_le_left) s =
      moduleRes M inf_le_left t) : s=t := by
  let F : TopCat.Sheaf AddCommGrpCat X := ⟨M.presheaf,M.isSheaf⟩
  apply F.eq_of_locally_eq' (fun i=>W⊓U i) W
    (fun _=>homOfLE inf_le_left) _ s t h
  intro x hx
  obtain ⟨i,hi⟩ := hcover x
  exact Opens.mem_iSup.mpr ⟨i,hx,hi⟩

theorem moduleSections_subsingleton_of_empty (M : X.Modules)
    (U : X.Opens) (hU : U=⊥) : Subsingleton Γ(M,U) := by
  refine ⟨fun s t=>?_⟩
  let F : TopCat.Sheaf AddCommGrpCat X := ⟨M.presheaf,M.isSheaf⟩
  apply F.eq_of_locally_eq' (fun _ : Empty=> (⊥ : X.Opens)) U
    (fun i=>nomatch i) (by simp [hU]) s t
  intro i
  exact Empty.elim i

namespace ModuleFrameGluing

variable {M N : X.Modules} {ι : Type v}
    (U : ι→X.Opens) (hcover : ∀ x : X,∃ i,x∈U i)
    (e : ∀ i,ModuleFrame M (U i)) (s : ∀ i,Γ(N,U i))

/-- The frame images respect the actual change of coordinates on every
smaller common open. -/
def Compatible : Prop :=
  ∀ i j (V : X.Opens) (hi : V≤U i) (hj : V≤U j),
    moduleRes N hi (s i) =
      (e j).coordinates V hj ((e i).generator V hi) • moduleRes N hj (s j)

def localImage (i : ι) (V : X.Opens) (hi : V≤U i) (t : Γ(M,V)) : Γ(N,V) :=
  (e i).coordinates V hi t • moduleRes N hi (s i)

theorem localImage_res (i : ι) {V W : X.Opens} (hi : V≤U i) (hWV : W≤V)
    (t : Γ(M,V)) :
    moduleRes N hWV (localImage U e s i V hi t) =
      localImage U e s i W (hWV.trans hi) (moduleRes M hWV t) := by
  rw [localImage,moduleRes_smul,moduleRes_trans,localImage,ModuleFrame.coordinates_res]

theorem localImage_eq (hs : Compatible U e s)
    (i j : ι) (V : X.Opens) (hi : V≤U i) (hj : V≤U j) (t : Γ(M,V)) :
    localImage U e s i V hi t = localImage U e s j V hj t := by
  unfold localImage
  rw [hs i j V hi hj,smul_smul,← (e i).coordinates_change (e j) hi hj t]

include hcover in
theorem exists_gluedSection (hs : Compatible U e s) (W : X.Opens) (t : Γ(M,W)) :
    ∃ g : Γ(N,W),∀ i,moduleRes N (show W⊓U i≤W from inf_le_left) g =
      localImage U e s i (W⊓U i) inf_le_right (moduleRes M inf_le_left t) := by
  let V (i : ι) := W⊓U i
  let a (i : ι) : Γ(N,V i) :=
    localImage U e s i (V i) inf_le_right (moduleRes M inf_le_left t)
  have ha : N.presheaf.IsCompatible V a := by
    intro i j
    change moduleRes N inf_le_left (a i) = moduleRes N inf_le_right (a j)
    dsimp only [a]
    rw [localImage_res,localImage_res,moduleRes_trans,moduleRes_trans]
    exact localImage_eq U e s hs i j (V i⊓V j) _ _ _
  let F : TopCat.Sheaf AddCommGrpCat X := ⟨N.presheaf,N.isSheaf⟩
  obtain ⟨g,hg,-⟩ := F.existsUnique_gluing' V W
    (fun _=>homOfLE inf_le_left) (by
      intro x hx
      obtain ⟨i,hi⟩ := hcover x
      exact Opens.mem_iSup.mpr ⟨i,hx,hi⟩) a ha
  exact ⟨g,hg⟩

def gluedSection (hs : Compatible U e s) (W : X.Opens) (t : Γ(M,W)) : Γ(N,W) :=
  (exists_gluedSection U hcover e s hs W t).choose

theorem gluedSection_res (hs : Compatible U e s) (W : X.Opens)
    (t : Γ(M,W)) (i : ι) :
    moduleRes N (show W⊓U i≤W from inf_le_left) (gluedSection U hcover e s hs W t) =
      localImage U e s i (W⊓U i) inf_le_right (moduleRes M inf_le_left t) :=
  (exists_gluedSection U hcover e s hs W t).choose_spec i

theorem gluedSection_res_local (hs : Compatible U e s) (W : X.Opens)
    (t : Γ(M,W)) (i : ι) (V : X.Opens) (hVW : V≤W) (hVi : V≤U i) :
    moduleRes N hVW (gluedSection U hcover e s hs W t) =
      localImage U e s i V hVi (moduleRes M hVW t) := by
  have hV : V≤W⊓U i := le_inf hVW hVi
  have h := congrArg (moduleRes N hV) (gluedSection_res U hcover e s hs W t i)
  simpa only [moduleRes_trans,localImage_res] using h

theorem gluedSection_add (hs : Compatible U e s) (W : X.Opens) (t v : Γ(M,W)) :
    gluedSection U hcover e s hs W (t+v) =
      gluedSection U hcover e s hs W t + gluedSection U hcover e s hs W v := by
  apply module_sections_ext_cover N U hcover W
  intro i
  simp only [gluedSection_res,map_add,localImage,map_add,add_smul]

theorem gluedSection_smul (hs : Compatible U e s) (W : X.Opens)
    (a : Γ(X,W)) (t : Γ(M,W)) :
    gluedSection U hcover e s hs W (a • t) =
      a • gluedSection U hcover e s hs W t := by
  apply module_sections_ext_cover N U hcover W
  intro i
  simp only [gluedSection_res,moduleRes_smul,localImage,map_smul,smul_eq_mul,smul_smul]

theorem gluedSection_natural (hs : Compatible U e s) {W V : X.Opens}
    (hVW : V≤W) (t : Γ(M,W)) :
    moduleRes N hVW (gluedSection U hcover e s hs W t) =
      gluedSection U hcover e s hs V (moduleRes M hVW t) := by
  apply module_sections_ext_cover N U hcover V
  intro i
  rw [moduleRes_trans,gluedSection_res_local U hcover e s hs W t i
    (V⊓U i) (inf_le_left.trans hVW) inf_le_right,
    gluedSection_res,moduleRes_trans]

/-- The actual sheaf morphism supplied by compatible images of a local
basis. It is built by the ordinary structure sheaf gluing axiom. -/
def hom (hs : Compatible U e s) : M ⟶ N where
  val.app W := ModuleCat.ofHom
    { toFun := gluedSection U hcover e s hs W.unop
      map_add' := gluedSection_add U hcover e s hs W.unop
      map_smul' := gluedSection_smul U hcover e s hs W.unop }
  val.naturality a := by
    ext t
    exact (gluedSection_natural U hcover e s hs a.unop.le t).symm

theorem hom_generator (hs : Compatible U e s) (i : ι) :
    (hom U hcover e s hs).app (U i) ((e i).generator (U i) le_rfl) = s i := by
  have h := gluedSection_res_local U hcover e s hs (U i)
    ((e i).generator (U i) le_rfl) i (U i) le_rfl le_rfl
  change gluedSection U hcover e s hs (U i) ((e i).generator (U i) le_rfl) = s i
  simpa only [moduleRes,homOfLE_refl,op_id,
    M.presheaf.map_id (op (U i)),N.presheaf.map_id (op (U i)),
    ConcreteCategory.id_apply,localImage,ModuleFrame.coordinates_generator,one_smul] using h

include hcover in
/-- An actual sheaf morphism is determined by the images of all local
frame generators on a cover. -/
theorem hom_ext (φ ψ : M ⟶ N)
    (h : ∀ i,φ.app (U i) ((e i).generator (U i) le_rfl) =
      ψ.app (U i) ((e i).generator (U i) le_rfl)) : φ=ψ := by
  apply Scheme.Modules.hom_ext
  intro W
  ext t
  apply module_sections_ext_cover N U hcover W
  intro i
  have hloc (φ : M ⟶ N) :
      moduleRes N (show W⊓U i≤W from inf_le_left) (φ.app W t) =
        (e i).coordinates (W⊓U i) inf_le_right (moduleRes M inf_le_left t) •
          moduleRes N inf_le_right (φ.app (U i) ((e i).generator (U i) le_rfl)) := by
    have hres :
        moduleRes N (show W⊓U i≤W from inf_le_left) (φ.app W t) =
          φ.app (W⊓U i) (moduleRes M inf_le_left t) :=
      (PresheafOfModules.naturality_apply φ.val
        (homOfLE (show W⊓U i≤W from inf_le_left)).op t).symm
    rw [hres]
    conv_lhs => rw [(e i).section_eq (W⊓U i) inf_le_right (moduleRes M inf_le_left t)]
    rw [Scheme.Modules.Hom.app_smul]
    congr 1
    rw [← ModuleFrame.generator_res (e i) (V := U i) (W := W⊓U i)
      le_rfl inf_le_right]
    exact PresheafOfModules.naturality_apply φ.val
      (homOfLE (show W⊓U i≤U i from inf_le_right)).op
      ((e i).generator (U i) le_rfl)
  rw [hloc φ,hloc ψ,h i]

theorem hom_unique (hs : Compatible U e s) (φ : M ⟶ N)
    (h : ∀ i,φ.app (U i) ((e i).generator (U i) le_rfl) = s i) :
    φ=hom U hcover e s hs :=
  hom_ext U hcover e φ (hom U hcover e s hs)
    (fun i=>(h i).trans (hom_generator U hcover e s hs i).symm)

end ModuleFrameGluing

end PaperVerification.ToricSchemes
end
end Source_ToricModuleFrameGluing
-- END ORIGINAL PaperVerification.ToricModuleFrameGluing


-- BEGIN ORIGINAL PaperVerification.ToricCartierPullbackFrames
section Source_ToricCartierPullbackFrames

-- original header: module

-- original header: public import PaperVerification.ToricModuleFrameGluing
-- original header: public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

-- original header: @[expose] public section

/-!
# Identification of the actual sheaf pullback by local frames

The target is identified with Mathlib's ordinary module-sheaf pullback by
its adjunction universal property. Compatible transition maps are used to
construct a genuine sheaf morphism; no pullback or section-space dictionary
is a field of a structure or an additional axiom. The statement applies to
closed immersions as well as dominant morphisms.
-/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace PaperVerification.ToricSchemes

open Scheme.Modules

variable {X Y : Scheme.{u}} (f : Y ⟶ X)
    {M : X.Modules} {N : Y.Modules} {ι : Type v}
    (U : ι→X.Opens) (hcover : ∀ x : X,∃ i,x∈U i)
    (e : ∀ i,ModuleFrame M (U i))
    (q : ∀ i,ModuleFrame N (f ⁻¹ᵁ U i))

include hcover in
theorem pullback_frameCover : ∀ y : Y,∃ i,y∈f ⁻¹ᵁ U i := fun y=>hcover (f y)

theorem pushforward_frameGenerator_res {F : Y.Modules}
    (β : M ⟶ (pushforward f).obj F) (i : ι)
    (V : X.Opens) (hV : V≤U i) :
    moduleRes F (f.preimage_mono hV)
        (β.app (U i) ((e i).generator (U i) le_rfl)) =
      β.app V ((e i).generator V hV) := by
  have h := PresheafOfModules.naturality_apply β.val (homOfLE hV).op
    ((e i).generator (U i) le_rfl)
  change β.app V (moduleRes M hV ((e i).generator (U i) le_rfl)) =
    moduleRes F (f.preimage_mono hV)
      (β.app (U i) ((e i).generator (U i) le_rfl)) at h
  exact h.symm.trans (congrArg (β.app V)
    ((e i).generator_res (V := U i) le_rfl hV))

variable (β₀ : M ⟶ (pushforward f).obj N)
    (hβ₀ : ∀ i,β₀.app (U i) ((e i).generator (U i) le_rfl) =
      (q i).generator (f ⁻¹ᵁ U i) le_rfl)

include β₀ hβ₀ in
/-- Any genuine morphism from the original sheaf supplies compatible
images of the comparison target's local generators. -/
theorem comparison_frameImages_compatible {F : Y.Modules}
    (β : M ⟶ (pushforward f).obj F) :
    ModuleFrameGluing.Compatible (fun i=>f ⁻¹ᵁ U i) q
      (fun i=>β.app (U i) ((e i).generator (U i) le_rfl)) := by
  intro i j W hWi hWj
  let V := U i⊓U j
  let c : Γ(X,V) := (e j).coordinates V inf_le_right ((e i).generator V inf_le_left)
  have hW : W≤f ⁻¹ᵁ V := by
    intro y hy
    exact ⟨hWi hy,hWj hy⟩
  have hgen : (e i).generator V inf_le_left =
      c • (e j).generator V inf_le_right :=
    (e j).section_eq V inf_le_right ((e i).generator V inf_le_left)
  have hβ (F : Y.Modules) (β : M ⟶ (pushforward f).obj F) :
      moduleRes F (f.preimage_mono (show V≤U i from inf_le_left))
          (β.app (U i) ((e i).generator (U i) le_rfl)) =
        f.app V c • moduleRes F (f.preimage_mono (show V≤U j from inf_le_right))
          (β.app (U j) ((e j).generator (U j) le_rfl)) := by
    rw [pushforward_frameGenerator_res f U e β i V inf_le_left,
      pushforward_frameGenerator_res f U e β j V inf_le_right,hgen,
      Scheme.Modules.Hom.app_smul]
    rfl
  have hN := hβ N β₀
  rw [hβ₀ i,hβ₀ j,ModuleFrame.generator_res,ModuleFrame.generator_res] at hN
  have hN' := congrArg (moduleRes N hW) hN
  rw [moduleRes_smul,ModuleFrame.generator_res,ModuleFrame.generator_res] at hN'
  have hc : (q j).coordinates W hWj ((q i).generator W hWi) =
      regularRes hW (f.app V c) := by
    rw [hN',_root_.map_smul,ModuleFrame.coordinates_generator,smul_eq_mul,mul_one]
  rw [hc]
  let hi : f ⁻¹ᵁ V≤f ⁻¹ᵁ U i := f.preimage_mono (show V≤U i from inf_le_left)
  let hj : f ⁻¹ᵁ V≤f ⁻¹ᵁ U j := f.preimage_mono (show V≤U j from inf_le_right)
  calc
    _ = moduleRes F hW (moduleRes F hi
        (β.app (U i) ((e i).generator (U i) le_rfl))) :=
      (moduleRes_trans F hi hW _).symm
    _ = moduleRes F hW (f.app V c • moduleRes F hj
        (β.app (U j) ((e j).generator (U j) le_rfl))) :=
      congrArg (moduleRes F hW) (hβ F β)
    _ = regularRes hW (f.app V c) • moduleRes F hW (moduleRes F hj
        (β.app (U j) ((e j).generator (U j) le_rfl))) :=
      moduleRes_smul F hW _ _
    _ = _ := congrArg (fun z=>regularRes hW (f.app V c) • z)
      (moduleRes_trans F hj hW _)

/-- The unique candidate supplied by the actual gluing of local frame
images. Its codomain is an arbitrary genuine module sheaf. -/
def comparisonLift {F : Y.Modules} (β : M ⟶ (pushforward f).obj F) : N ⟶ F :=
  ModuleFrameGluing.hom (fun i=>f ⁻¹ᵁ U i) (pullback_frameCover f U hcover) q
    (fun i=>β.app (U i) ((e i).generator (U i) le_rfl))
    (comparison_frameImages_compatible f U e q β₀ hβ₀ β)

theorem comparisonLift_generator {F : Y.Modules}
    (β : M ⟶ (pushforward f).obj F) (i : ι) :
    (comparisonLift f U hcover e q β₀ hβ₀ β).app (f ⁻¹ᵁ U i)
        ((q i).generator (f ⁻¹ᵁ U i) le_rfl) =
      β.app (U i) ((e i).generator (U i) le_rfl) :=
  ModuleFrameGluing.hom_generator _ _ _ _ _ i

theorem comparison_comp_lift {F : Y.Modules}
    (β : M ⟶ (pushforward f).obj F) :
    β₀ ≫ (pushforward f).map (comparisonLift f U hcover e q β₀ hβ₀ β) = β := by
  apply ModuleFrameGluing.hom_ext U hcover e
  intro i
  change (comparisonLift f U hcover e q β₀ hβ₀ β).app (f ⁻¹ᵁ U i)
    (β₀.app (U i) ((e i).generator (U i) le_rfl)) = _
  rw [hβ₀ i,comparisonLift_generator]

include hcover e q hβ₀ in
theorem comparison_postcompose_bijective (F : Y.Modules) :
    Function.Bijective (fun h : N ⟶ F=>β₀ ≫ (pushforward f).map h) := by
  constructor
  · intro h l heq
    apply ModuleFrameGluing.hom_ext (fun i=>f ⁻¹ᵁ U i)
      (pullback_frameCover f U hcover) q
    intro i
    have hEval := congrArg (fun a : M ⟶ (pushforward f).obj F =>
      a.app (U i) ((e i).generator (U i) le_rfl)) heq
    change h.app (f ⁻¹ᵁ U i) (β₀.app (U i) ((e i).generator (U i) le_rfl)) =
      l.app (f ⁻¹ᵁ U i) (β₀.app (U i) ((e i).generator (U i) le_rfl)) at hEval
    simpa only [hβ₀ i] using hEval
  · intro β
    exact ⟨comparisonLift f U hcover e q β₀ hβ₀ β,
      comparison_comp_lift f U hcover e q β₀ hβ₀ β⟩

include hcover e q hβ₀ in
/-- The actual adjoint morphism is an isomorphism because it has the
genuine universal property of the module-sheaf pullback. -/
theorem pullback_comparison_isIso :
    IsIso (((pullbackPushforwardAdjunction f).homEquiv M N).symm β₀) := by
  let α := ((pullbackPushforwardAdjunction f).homEquiv M N).symm β₀
  rw [isIso_iff_coyoneda_map_bijective]
  intro F
  change Function.Bijective (fun h : N ⟶ F=>α ≫ h)
  let E := (pullbackPushforwardAdjunction f).homEquiv M F
  have hcomp (h : N ⟶ F) : E (α ≫ h)=β₀ ≫ (pushforward f).map h := by
    rw [Adjunction.homEquiv_naturality_right,Equiv.apply_symm_apply]
  have hb := comparison_postcompose_bijective f U hcover e q β₀ hβ₀ F
  constructor
  · intro h l heq
    apply hb.injective
    exact (hcomp h).symm.trans ((congrArg E heq).trans (hcomp l))
  · intro γ
    obtain ⟨h,hh⟩ := hb.surjective (E γ)
    refine ⟨h,E.injective ?_⟩
    exact (hcomp h).trans hh

/-- A shared criterion for arbitrary scheme morphisms: an actual map
sending one local basis to the other identifies the actual pullback. -/
def pullbackIso_of_frameComparison : (pullback f).obj M ≅ N := by
  letI := pullback_comparison_isIso f U hcover e q β₀ hβ₀
  exact asIso (((pullbackPushforwardAdjunction f).homEquiv M N).symm β₀)

section CompatibleTransitions

variable
    (htrans : ModuleFrameGluing.Compatible (N := (pushforward f).obj N) U e
      (fun i=>(q i).generator (f ⁻¹ᵁ U i) le_rfl))

/-- Mapped regular transition functions construct the comparison itself;
the existence of this sheaf map is not assumed. -/
def framePullbackComparison : M ⟶ (pushforward f).obj N :=
  ModuleFrameGluing.hom U hcover e
    (fun i=>(q i).generator (f ⁻¹ᵁ U i) le_rfl) htrans

/-- Local frames with genuinely mapped transition functions identify the
ordinary sheaf pullback, also along a closed boundary immersion. -/
def pullbackIso_of_compatible_frames : (pullback f).obj M ≅ N :=
  pullbackIso_of_frameComparison f U hcover e q
    (framePullbackComparison f U hcover e q htrans)
    (ModuleFrameGluing.hom_generator U hcover e _ htrans)

end CompatibleTransitions

end PaperVerification.ToricSchemes
end
end Source_ToricCartierPullbackFrames
-- END ORIGINAL PaperVerification.ToricCartierPullbackFrames


-- BEGIN ORIGINAL PaperVerification.ToricCartierAmple
section Source_ToricCartierAmple

-- original header: module

-- original header: public import PaperVerification.ToricCartierProducts
-- original header: public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

-- original header: @[expose] public section

/-!
# Intrinsic nonvanishing and ampleness of actual Cartier sheaves

The nonvanishing open is computed from actual regular coordinates in local
frames. Its membership is independent of the frame, and is exactly the
condition that the local coefficient is outside the maximal ideal of the
actual local ring. Ampleness uses the standard affine nonvanishing-open
definition (EGA II, Definition 4.5.3; Stacks Project, tag 01PS).

No fan, polytope, support-function inequality, or section-space formula is
part of this definition. Powers use powers of actual local Cartier equations;
the tensor-sheaf identification is developed separately.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace PaperVerification.ToricSchemes

variable {X : Scheme.{u}} [IsIntegral X]

/-- The usual unit condition in an actual local ring, expressed through its
injective embedding in the actual function field. -/
theorem isUnit_stalk_iff (x : X) (a : X.presheaf.stalk x) :
    IsUnit a ↔
      algebraMap (X.presheaf.stalk x) X.functionField a ≠ 0 ∧
      (algebraMap (X.presheaf.stalk x) X.functionField a)⁻¹ ∈ regularAtSubring X x := by
  constructor
  · rintro ⟨u,rfl⟩
    have hne : algebraMap (X.presheaf.stalk x) X.functionField (u : X.presheaf.stalk x)≠0 :=
      ((u.isUnit).map (algebraMap (X.presheaf.stalk x) X.functionField)).ne_zero
    refine ⟨hne,⟨(u⁻¹ : (X.presheaf.stalk x)ˣ),?_⟩⟩
    apply mul_left_cancel₀ hne
    rw [← map_mul,u.mul_inv,map_one,mul_inv_cancel₀ hne]
  · rintro ⟨hne,b,hb⟩
    have hab : a*b=1 := by
      apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
      rw [map_mul,hb,map_one,mul_inv_cancel₀ hne]
    exact ⟨⟨a,b,hab,by simpa only [mul_comm] using hab⟩,rfl⟩

namespace RationalCartierCocycle

variable (C D : RationalCartierCocycle X)

/-- Natural powers of the actual local rational generators. -/
def pow (n : ℕ) : RationalCartierCocycle X where
  index := C.index
  openSet := C.openSet
  covers := C.covers
  generator i := C.generator i ^ n
  transition i j x hi hj := by
    simpa only [Units.val_pow_eq_pow_val,div_pow] using
      (regularAtSubring X x).pow_mem (C.transition i j x hi hj) n

@[simp] theorem pow_openSet (n : ℕ) (i : C.index) :
    (C.pow n).openSet i=C.openSet i := rfl

@[simp] theorem pow_generator (n : ℕ) (i : C.index) :
    ((C.pow n).generator i : X.functionField)=(C.generator i : X.functionField)^n := rfl

/-- The actual regular coefficient of a global section in a local frame. -/
def localCoefficient (i : C.index) (s : Γ(C.sheaf,⊤)) : Γ(X,C.openSet i) :=
  C.localCoordinates i (C.openSet i) le_rfl
    (C.sheaf.presheaf.map (homOfLE le_top).op s)

theorem localCoefficient_value (i : C.index) [Nonempty (C.openSet i)]
    (s : Γ(C.sheaf,⊤)) :
    X.germToFunctionField (C.openSet i) (C.localCoefficient i s) =
      C.toCartierData.sectionValue ⊤ s / (C.generator i : X.functionField) := by
  rw [localCoefficient,C.localCoordinates_value]
  change rationalValue X (C.openSet i)
      ((rationalFunctions X).presheaf.map (homOfLE le_top).op s.val) /
        (C.generator i : X.functionField) =
    rationalValue X ⊤ s.val / (C.generator i : X.functionField)
  exact congrArg (fun z : X.functionField => z / (C.generator i : X.functionField))
    (rationalValue_restrict X (homOfLE (show C.openSet i≤⊤ from le_top)) s.val)

/-- The usual nonvanishing locus of a section, as an actual open set. -/
def nonvanishingOpen (s : Γ(C.sheaf,⊤)) : X.Opens :=
  ⨆ i,X.basicOpen (C.localCoefficient i s)

/-- In any chosen local frame, nonvanishing is the actual local unit test. -/
theorem mem_localNonvanishing_iff (i : C.index) (s : Γ(C.sheaf,⊤))
    (x : X) (hxi : x∈C.openSet i) :
    x∈X.basicOpen (C.localCoefficient i s) ↔
      C.toCartierData.sectionValue ⊤ s ≠ 0 ∧
      (C.generator i : X.functionField)/C.toCartierData.sectionValue ⊤ s ∈
        regularAtSubring X x := by
  letI : Nonempty (C.openSet i) := ⟨⟨x,hxi⟩⟩
  rw [X.mem_basicOpen _ x hxi,isUnit_stalk_iff,
    X.algebraMap_germ_eq_germToFunctionField hxi,C.localCoefficient_value]
  rw [div_ne_zero_iff,inv_div]
  constructor
  · rintro ⟨⟨h,-⟩,hr⟩
    exact ⟨h,hr⟩
  · rintro ⟨h,hr⟩
    exact ⟨⟨h,(C.generator i).ne_zero⟩,hr⟩

/-- The local nonvanishing condition agrees on overlaps. -/
theorem localNonvanishing_iff (i j : C.index) (s : Γ(C.sheaf,⊤))
    (x : X) (hxi : x∈C.openSet i) (hxj : x∈C.openSet j) :
    x∈X.basicOpen (C.localCoefficient i s) ↔
      x∈X.basicOpen (C.localCoefficient j s) := by
  rw [C.mem_localNonvanishing_iff i s x hxi,
    C.mem_localNonvanishing_iff j s x hxj]
  constructor
  · rintro ⟨hr,h⟩
    refine ⟨hr,?_⟩
    have hratio := C.transition j i x hxj hxi
    have he : ((C.generator j : X.functionField)/(C.generator i : X.functionField))*
        ((C.generator i : X.functionField)/C.toCartierData.sectionValue ⊤ s) =
        (C.generator j : X.functionField)/C.toCartierData.sectionValue ⊤ s := by
      field_simp [Units.ne_zero,hr]
    simpa only [he] using (regularAtSubring X x).mul_mem hratio h
  · rintro ⟨hr,h⟩
    refine ⟨hr,?_⟩
    have hratio := C.transition i j x hxi hxj
    have he : ((C.generator i : X.functionField)/(C.generator j : X.functionField))*
        ((C.generator j : X.functionField)/C.toCartierData.sectionValue ⊤ s) =
        (C.generator i : X.functionField)/C.toCartierData.sectionValue ⊤ s := by
      field_simp [Units.ne_zero,hr]
    simpa only [he] using (regularAtSubring X x).mul_mem hratio h

/-- A frame-independent membership test for the actual nonvanishing open. -/
theorem mem_nonvanishingOpen_iff (i : C.index) (s : Γ(C.sheaf,⊤))
    (x : X) (hxi : x∈C.openSet i) :
    x∈C.nonvanishingOpen s ↔
      IsUnit (X.presheaf.germ (C.openSet i) x hxi (C.localCoefficient i s)) := by
  rw [← X.mem_basicOpen _ x hxi]
  constructor
  · intro hx
    obtain ⟨j,hj⟩ := Opens.mem_iSup.mp hx
    exact (C.localNonvanishing_iff j i s x (X.basicOpen_le _ hj) hxi).mp hj
  · intro hx
    exact Opens.mem_iSup.mpr ⟨i,hx⟩

/-- In the actual local rank-one coordinate, the section is nonvanishing
exactly when it is outside the maximal ideal. This is the ordinary fibre
criterion, without interpreting nonvanishing as a formal support inequality. -/
theorem mem_nonvanishingOpen_iff_not_mem_maximalIdeal
    (i : C.index) (s : Γ(C.sheaf,⊤)) (x : X) (hxi : x∈C.openSet i) :
    x∈C.nonvanishingOpen s ↔
      X.presheaf.germ (C.openSet i) x hxi (C.localCoefficient i s) ∉
        IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  rw [C.mem_nonvanishingOpen_iff i s x hxi,IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff,not_not]

/-- A power of an actual rational section is an actual section of the
corresponding power of its Cartier sheaf. -/
def sectionPow (n : ℕ) (s : Γ(C.sheaf,⊤)) : Γ((C.pow n).sheaf,⊤) := by
  let t : Γ(rationalFunctions X,⊤) :=
    (show Γ(Spec X.functionField,genericPointMap X ⁻¹ᵁ (⊤ : X.Opens)) from s.val)^n
  refine ⟨t,?_⟩
  intro i x hx
  have hs : rationalValue X ⊤ s.val / (C.generator i : X.functionField) ∈
      regularAtSubring X x.val := s.property i x hx
  have h := (regularAtSubring X x.val).pow_mem hs n
  have ht : rationalValue X ⊤ t = (rationalValue X ⊤ s.val)^n :=
    map_pow (rationalSectionValueIso X ⊤).hom.hom
      (show Γ(Spec X.functionField,genericPointMap X ⁻¹ᵁ (⊤ : X.Opens)) from s.val) n
  change rationalValue X ⊤ t / (C.generator i : X.functionField)^n ∈ regularAtSubring X x.val
  rw [ht]
  simpa only [div_pow] using h

@[simp] theorem sectionPow_value (n : ℕ) (s : Γ(C.sheaf,⊤)) :
    (C.pow n).toCartierData.sectionValue ⊤ (C.sectionPow n s) =
      (C.toCartierData.sectionValue ⊤ s)^n :=
  map_pow (rationalSectionValueIso X ⊤).hom.hom
    (show Γ(Spec X.functionField,genericPointMap X ⁻¹ᵁ (⊤ : X.Opens)) from s.val) n

theorem localCoefficient_sectionPow (n : ℕ) (i : C.index)
    (s : Γ(C.sheaf,⊤)) :
    (C.pow n).localCoefficient i (C.sectionPow n s) = (C.localCoefficient i s)^n := by
  classical
  by_cases hU : Nonempty (C.openSet i)
  · letI := hU
    letI : Nonempty ((C.pow n).openSet i) := by
      change Nonempty (C.openSet i)
      exact hU
    apply X.germToFunctionField_injective (C.openSet i)
    calc
      _ = (C.pow n).toCartierData.sectionValue ⊤ (C.sectionPow n s) /
          (C.generator i : X.functionField)^n :=
        (C.pow n).localCoefficient_value i (C.sectionPow n s)
      _ = (C.toCartierData.sectionValue ⊤ s)^n / (C.generator i : X.functionField)^n :=
        congrArg (fun z : X.functionField => z / (C.generator i : X.functionField)^n)
          (C.sectionPow_value n s)
      _ = (C.toCartierData.sectionValue ⊤ s / (C.generator i : X.functionField))^n :=
        (div_pow _ _ n).symm
      _ = (X.germToFunctionField (C.openSet i) (C.localCoefficient i s))^n :=
        congrArg (fun z : X.functionField => z^n) (C.localCoefficient_value i s).symm
      _ = _ := (map_pow (X.germToFunctionField (C.openSet i)).hom _ n).symm
  · have hbot : C.openSet i=⊥ := by
      apply le_antisymm ?_ bot_le
      intro x hx
      exact (hU ⟨⟨x,hx⟩⟩).elim
    letI := regularSections_subsingleton_of_empty X (C.openSet i) hbot
    change (_ : Γ(X,C.openSet i)) = _
    exact Subsingleton.elim _ _

/-- Raising a section to a positive power preserves its actual nonvanishing
open, exactly as for regular functions. -/
theorem nonvanishingOpen_sectionPow (n : ℕ) (hn : 0<n) (s : Γ(C.sheaf,⊤)) :
    (C.pow n).nonvanishingOpen (C.sectionPow n s)=C.nonvanishingOpen s := by
  change (⨆ i : C.index,X.basicOpen ((C.pow n).localCoefficient i (C.sectionPow n s))) =
    ⨆ i : C.index,X.basicOpen (C.localCoefficient i s)
  apply iSup_congr
  intro i
  exact (congrArg (fun t : Γ(X,C.openSet i) => X.basicOpen t)
    (C.localCoefficient_sectionPow n i s)).trans (X.basicOpen_pow _ hn)

/-- The standard intrinsic definition of an ample Cartier sheaf. Compactness
here is quasi-compactness of the underlying spectral topological space. -/
def IsAmple : Prop :=
  CompactSpace X ∧ ∀ x : X,∃ n : ℕ,0<n ∧
    ∃ s : Γ((C.pow n).sheaf,⊤),
      x∈(C.pow n).nonvanishingOpen s ∧ IsAffineOpen ((C.pow n).nonvanishingOpen s)

/-- Ampleness supplies a finite affine cover by genuine nonvanishing opens
of positive tensor powers. -/
theorem IsAmple.exists_finite_cover (hC : C.IsAmple) :
    ∃ (ι : Type u) (_ : Fintype ι) (n : ι→ℕ)
      (s : ∀ i,Γ((C.pow (n i)).sheaf,⊤)),
      (∀ i,0<n i) ∧
      (∀ i,IsAffineOpen ((C.pow (n i)).nonvanishingOpen (s i))) ∧
      (⨆ i,(C.pow (n i)).nonvanishingOpen (s i))=⊤ := by
  classical
  letI := hC.1
  choose n hn s hs ha using hC.2
  have hcover : IsOpenCover (fun x:X=>(C.pow (n x)).nonvanishingOpen (s x)) := by
    apply le_antisymm le_top
    intro x hx
    exact Opens.mem_iSup.mpr ⟨x,hs x⟩
  obtain ⟨t,ht⟩ := hcover.exists_finite_of_compactSpace
  exact ⟨t,inferInstance,fun i=>n i.val,fun i=>s i.val,
    fun i=>hn i.val,fun i=>ha i.val,ht⟩

end RationalCartierCocycle

namespace CartierData

variable (D : CartierData X)

/-- Multiplication of a Cartier divisor by a natural number. -/
def nsmul (n : ℕ) : CartierData X := (D.localCocycle.pow n).toCartierData

/-- Intrinsic ampleness, without any fan or polytope hypothesis. -/
def IsAmple : Prop := D.localCocycle.IsAmple

end CartierData

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.mem_nonvanishingOpen_iff_not_mem_maximalIdeal
#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.nonvanishingOpen_sectionPow
#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.IsAmple.exists_finite_cover
end
end Source_ToricCartierAmple
-- END ORIGINAL PaperVerification.ToricCartierAmple


-- BEGIN ORIGINAL PaperVerification.ToricCartierTranslate
section Source_ToricCartierTranslate

-- original header: module

-- original header: public import PaperVerification.ToricCartierAmple
-- original header: public import Mathlib.Algebra.Module.Equiv.Basic

-- original header: @[expose] public section

/-!
# Principal translates and linear equivalence of actual Cartier sheaves

A nonzero rational function acts by an actual automorphism of the rational
function sheaf. Postcomposing a fractional embedding by this automorphism
changes the Cartier divisor by a principal divisor, while preserving its
actual invertible sheaf. This is linear equivalence, distinguished from the
embedding-preserving equivalence of presentations of the same divisor.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace PaperVerification.ToricSchemes

variable {X : Scheme.{u}} [IsIntegral X]

def rationalScaleEquivNonempty (q : X.functionFieldˣ) (U : X.Opens) [Nonempty U] :
    Γ(rationalFunctions X,U) ≃ₗ[Γ(X,U)] Γ(rationalFunctions X,U) := by
  let e : X.functionField ≃ₗ[X.functionField] X.functionField :=
    LinearEquiv.smulOfUnit q
  exact (rationalValueLinearEquiv X U).trans
    ((e.restrictScalars Γ(X,U)).trans (rationalValueLinearEquiv X U).symm)

def rationalScaleEquiv (q : X.functionFieldˣ) (U : X.Opens) :
    Γ(rationalFunctions X,U) ≃ₗ[Γ(X,U)] Γ(rationalFunctions X,U) := by
  classical
  by_cases hU : Nonempty U
  · letI := hU
    exact rationalScaleEquivNonempty q U
  · exact LinearEquiv.refl _ _

@[simp] theorem rationalScaleEquiv_value (q : X.functionFieldˣ)
    (U : X.Opens) [Nonempty U] (s : Γ(rationalFunctions X,U)) :
    rationalValue X U (rationalScaleEquiv q U s) =
      (q : X.functionField)*rationalValue X U s := by
  simp only [rationalScaleEquiv,dif_pos (show Nonempty U from inferInstance)]
  change (rationalValueLinearEquiv X U)
      ((rationalValueLinearEquiv X U).symm
        ((q : X.functionField) * (rationalValueLinearEquiv X U) s)) =
    (q : X.functionField) * (rationalValueLinearEquiv X U) s
  exact (rationalValueLinearEquiv X U).apply_symm_apply _

theorem rationalScaleEquiv_restrict (q : X.functionFieldˣ)
    {U V : X.Opens} (i : V ⟶ U) (s : Γ(rationalFunctions X,U)) :
    rationalScaleEquiv q V ((rationalFunctions X).presheaf.map i.op s) =
      (rationalFunctions X).presheaf.map i.op (rationalScaleEquiv q U s) := by
  classical
  by_cases hV : Nonempty V
  · letI := hV
    letI : Nonempty U := ⟨⟨(Classical.choice hV).val,i.le (Classical.choice hV).property⟩⟩
    apply (rationalValue X V).injective
    rw [rationalScaleEquiv_value,rationalValue_restrict,rationalValue_restrict,
      rationalScaleEquiv_value]
  · have hbot : V=⊥ := by
      apply le_antisymm ?_ bot_le
      intro x hx
      exact (hV ⟨⟨x,hx⟩⟩).elim
    letI := regularSections_subsingleton_of_empty X V hbot
    letI := Module.subsingleton Γ(X,V) Γ(rationalFunctions X,V)
    exact Subsingleton.elim _ _

/-- Multiplication by a rational unit is an actual sheaf automorphism. -/
def rationalScaleIso (q : X.functionFieldˣ) : rationalFunctions X ≅ rationalFunctions X :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk (fun U=>(rationalScaleEquiv q U.unop).toModuleIso)
      (by
        intro U V f
        ext s
        exact rationalScaleEquiv_restrict q f.unop s)

namespace CartierData

variable (D E F : CartierData X)

/-- Linear equivalence records an isomorphism of the actual invertible
sheaves. It does not require equality of their rational embeddings. -/
def LinearlyEquivalent : Prop := Nonempty (D.sheaf ≅ E.sheaf)

theorem linearlyEquivalent_refl : D.LinearlyEquivalent D := ⟨Iso.refl _⟩

theorem linearlyEquivalent_symm (h : D.LinearlyEquivalent E) : E.LinearlyEquivalent D :=
  ⟨h.some.symm⟩

theorem linearlyEquivalent_trans (hDE : D.LinearlyEquivalent E)
    (hEF : E.LinearlyEquivalent F) : D.LinearlyEquivalent F := ⟨hDE.some ≪≫ hEF.some⟩

theorem Equivalent.linearlyEquivalent (h : D.Equivalent E) : D.LinearlyEquivalent E :=
  ⟨h.choose⟩

/-- Principal translation multiplies the actual fractional embedding by q.
The underlying actual sheaf is unchanged by construction. -/
def scale (q : X.functionFieldˣ) : CartierData X where
  sheaf := D.sheaf
  inclusion := D.inclusion ≫ (rationalScaleIso q).hom
  inclusion_injective U :=
    (rationalScaleEquiv q U).injective.comp (D.inclusion_injective U)
  locallyFree := D.locallyFree

def scaleSheafIso (q : X.functionFieldˣ) : (D.scale q).sheaf ≅ D.sheaf := Iso.refl _

theorem scale_linearlyEquivalent (q : X.functionFieldˣ) :
    (D.scale q).LinearlyEquivalent D := ⟨D.scaleSheafIso q⟩

@[simp] theorem scale_sectionValue (q : X.functionFieldˣ)
    (U : X.Opens) [Nonempty U] (s : Γ(D.sheaf,U)) :
    (D.scale q).sectionValue U s = (q : X.functionField)*D.sectionValue U s :=
  rationalScaleEquiv_value q U (D.inclusion.app U s)

theorem scale_equivalent_scale (h : D.Equivalent E) (q : X.functionFieldˣ) :
    (D.scale q).Equivalent (E.scale q) := by
  obtain ⟨e,he⟩ := h
  refine ⟨e,?_⟩
  change e.hom ≫ (E.inclusion ≫ (rationalScaleIso q).hom) =
    D.inclusion ≫ (rationalScaleIso q).hom
  rw [← Category.assoc,he]

/-- The principal translation changes every local rational generator by
the same explicit factor, so no character shift is lost. -/
theorem scale_frameRationalGenerator (q : X.functionFieldˣ)
    {U : X.Opens} [Nonempty U] (e : D.Frame U) :
    (D.scale q).frameRationalGenerator e =
      (q : X.functionField)*D.frameRationalGenerator e :=
  D.scale_sectionValue q U (D.frameGenerator e U le_rfl)

end CartierData

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.rationalScaleIso
#print axioms PaperVerification.ToricSchemes.CartierData.scale_linearlyEquivalent
#print axioms PaperVerification.ToricSchemes.CartierData.scale_frameRationalGenerator
end
end Source_ToricCartierTranslate
-- END ORIGINAL PaperVerification.ToricCartierTranslate


-- BEGIN ORIGINAL PaperVerification.ToricCartierDescent
section Source_ToricCartierDescent

-- original header: module

-- original header: public import PaperVerification.ToricCartierTranslate

-- original header: @[expose] public section

/-!
# Descent of Cartier arithmetic through equality of presentations

Regular ratios of genuine local generators give inclusions of the actual
fractional sheaves. Ratios regular in both directions give an isomorphism
preserving the rational embedding. This proves that products, inverses and
powers descend through equality of Cartier-divisor presentations.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace PaperVerification.ToricSchemes

variable {X : Scheme.{u}} [IsIntegral X]

namespace RationalCartierCocycle

variable (C D E F : RationalCartierCocycle X)

/-- Every local generator of C is a regular multiple of every local
generator of D wherever the two local frames overlap. -/
def GeneratorRatioRegular : Prop :=
  ∀ i j (x : X),x∈C.openSet i → x∈D.openSet j →
    (C.generator i : X.functionField)/(D.generator j : X.functionField) ∈
      regularAtSubring X x

theorem generatorRatioRegular_refl : C.GeneratorRatioRegular C := C.transition

theorem isSection_mono (h : C.GeneratorRatioRegular D)
    (U : X.Opens) (s : Γ(rationalFunctions X,U)) (hs : C.IsSection U s) :
    D.IsSection U s := by
  intro j x hxj
  obtain ⟨i,hxi⟩ := C.covers x.val
  have ht := h i j x.val hxi hxj
  have hc := hs i x hxi
  have he : (rationalValueAt X U x s/(C.generator i : X.functionField))*
      ((C.generator i : X.functionField)/(D.generator j : X.functionField)) =
      rationalValueAt X U x s/(D.generator j : X.functionField) := by
    field_simp [Units.ne_zero]
  simpa only [he] using (regularAtSubring X x.val).mul_mem hc ht

def sameGeneratorSheafLinearEquiv
    (hCD : C.GeneratorRatioRegular D) (hDC : D.GeneratorRatioRegular C)
    (U : X.Opens) : Γ(C.sheaf,U) ≃ₗ[Γ(X,U)] Γ(D.sheaf,U) where
  toFun s := ⟨s.val,C.isSection_mono D hCD U s.val s.property⟩
  invFun s := ⟨s.val,D.isSection_mono C hDC U s.val s.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Equality of the actual fractional subsheaves, with the same rational
values under the resulting sheaf isomorphism. -/
def sameGeneratorSheafIso
    (hCD : C.GeneratorRatioRegular D) (hDC : D.GeneratorRatioRegular C) :
    C.sheaf ≅ D.sheaf :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk
      (fun U=>(C.sameGeneratorSheafLinearEquiv D hCD hDC U.unop).toModuleIso)
      (by intros; rfl)

theorem equivalent_of_generatorRatios
    (hCD : C.GeneratorRatioRegular D) (hDC : D.GeneratorRatioRegular C) :
    C.toCartierData.Equivalent D.toCartierData := by
  refine ⟨C.sameGeneratorSheafIso D hCD hDC,?_⟩
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  rfl

theorem GeneratorRatioRegular.mul
    (hCD : C.GeneratorRatioRegular D) (hEF : E.GeneratorRatioRegular F) :
    (C.mul E).GeneratorRatioRegular (D.mul F) := by
  intro i j x hxi hxj
  have h₁ := hCD i.1 j.1 x hxi.1 hxj.1
  have h₂ := hEF i.2 j.2 x hxi.2 hxj.2
  change ((C.generator i.1 : X.functionField) * (E.generator i.2 : X.functionField)) /
    ((D.generator j.1 : X.functionField) * (F.generator j.2 : X.functionField)) ∈
      regularAtSubring X x
  simpa only [div_mul_div_comm] using
    (regularAtSubring X x).mul_mem h₁ h₂

theorem GeneratorRatioRegular.inv (hDC : D.GeneratorRatioRegular C) :
    C.inv.GeneratorRatioRegular D.inv := by
  intro i j x hxi hxj
  change (((C.generator i)⁻¹ : X.functionFieldˣ) : X.functionField) /
    (((D.generator j)⁻¹ : X.functionFieldˣ) : X.functionField) ∈ regularAtSubring X x
  simpa only [Units.val_inv_eq_inv_val,inv_div_inv] using hDC j i x hxj hxi

theorem GeneratorRatioRegular.pow (hCD : C.GeneratorRatioRegular D) (n : ℕ) :
    (C.pow n).GeneratorRatioRegular (D.pow n) := by
  intro i j x hxi hxj
  change (C.generator i : X.functionField)^n /
    (D.generator j : X.functionField)^n ∈ regularAtSubring X x
  simpa only [div_pow] using
    (regularAtSubring X x).pow_mem (hCD i j x hxi hxj) n

end RationalCartierCocycle

namespace CartierData

variable (D D' E E' : CartierData X)

set_option backward.isDefEq.respectTransparency false in
/-- Equality of actual fractional sheaves makes all cross-frame ratios
regular in the actual local rings. -/
theorem localCocycle_generatorRatios (h : D.Equivalent D') :
    D.localCocycle.GeneratorRatioRegular D'.localCocycle := by
  intro i j x hxi hxj
  let U := invertibleOpen D.locallyFree i
  let W := invertibleOpen D'.locallyFree j
  let V : X.Opens := U⊓W
  letI : Nonempty U := ⟨⟨i,mem_invertibleOpen D.locallyFree i⟩⟩
  letI : Nonempty W := ⟨⟨j,mem_invertibleOpen D'.locallyFree j⟩⟩
  letI : Nonempty V := ⟨⟨x,hxi,hxj⟩⟩
  have hq : D.frameRationalGenerator (invertibleFrame D.locallyFree i) ∈
      D.sectionValueRange V :=
    ⟨D.frameGenerator (invertibleFrame D.locallyFree i) V inf_le_left,
      D.sectionValue_frameGenerator _ inf_le_left⟩
  rw [D.equivalent_sectionValueRange D' h V] at hq
  obtain ⟨a,ha⟩ :=
    (D'.mem_sectionValueRange_iff (invertibleFrame D'.locallyFree j)
      (V := V) inf_le_right _).mp hq
  have ha' : X.germToFunctionField V a =
      D.frameRationalGenerator (invertibleFrame D.locallyFree i) /
        D'.frameRationalGenerator (invertibleFrame D'.locallyFree j) :=
    (eq_div_iff (D'.frameRationalGenerator_ne_zero _)).mpr ha
  change D.frameRationalGenerator (invertibleFrame D.locallyFree i) /
    D'.frameRationalGenerator (invertibleFrame D'.locallyFree j) ∈ regularAtSubring X x
  rw [← ha']
  exact regular_germ_mem_regularAt X V a x ⟨hxi,hxj⟩

theorem add_equivalent_add (hD : D.Equivalent D') (hE : E.Equivalent E') :
    (D.add E).Equivalent (D'.add E') :=
  (D.localCocycle.mul E.localCocycle).equivalent_of_generatorRatios
    (D'.localCocycle.mul E'.localCocycle)
    (RationalCartierCocycle.GeneratorRatioRegular.mul
      D.localCocycle D'.localCocycle E.localCocycle E'.localCocycle
      (D.localCocycle_generatorRatios D' hD) (E.localCocycle_generatorRatios E' hE))
    (RationalCartierCocycle.GeneratorRatioRegular.mul
      D'.localCocycle D.localCocycle E'.localCocycle E.localCocycle
      (D'.localCocycle_generatorRatios D (D.equivalent_symm D' hD))
      (E'.localCocycle_generatorRatios E (E.equivalent_symm E' hE)))

theorem neg_equivalent_neg (hD : D.Equivalent D') :
    D.neg.Equivalent D'.neg :=
  D.localCocycle.inv.equivalent_of_generatorRatios D'.localCocycle.inv
    (RationalCartierCocycle.GeneratorRatioRegular.inv D.localCocycle D'.localCocycle
      (D'.localCocycle_generatorRatios D (D.equivalent_symm D' hD)))
    (RationalCartierCocycle.GeneratorRatioRegular.inv D'.localCocycle D.localCocycle
      (D.localCocycle_generatorRatios D' hD))

theorem nsmul_equivalent_nsmul (hD : D.Equivalent D') (n : ℕ) :
    (D.nsmul n).Equivalent (D'.nsmul n) :=
  (D.localCocycle.pow n).equivalent_of_generatorRatios (D'.localCocycle.pow n)
    (RationalCartierCocycle.GeneratorRatioRegular.pow D.localCocycle D'.localCocycle
      (D.localCocycle_generatorRatios D' hD) n)
    (RationalCartierCocycle.GeneratorRatioRegular.pow D'.localCocycle D.localCocycle
      (D'.localCocycle_generatorRatios D (D.equivalent_symm D' hD)) n)

end CartierData

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.equivalent_of_generatorRatios
#print axioms PaperVerification.ToricSchemes.CartierData.add_equivalent_add
#print axioms PaperVerification.ToricSchemes.CartierData.neg_equivalent_neg
#print axioms PaperVerification.ToricSchemes.CartierData.nsmul_equivalent_nsmul
end
end Source_ToricCartierDescent
-- END ORIGINAL PaperVerification.ToricCartierDescent


-- BEGIN ORIGINAL PaperVerification.ToricCartierRangeEquality
section Source_ToricCartierRangeEquality

-- original header: module

-- original header: public import PaperVerification.ToricCartierDescent

-- original header: @[expose] public section

/-! # Local equality of actual fractional sheaves detects Cartier equality -/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace PaperVerification.ToricSchemes.CartierData

variable {X : Scheme.{u}} [IsIntegral X] (D E : CartierData X)

set_option backward.isDefEq.respectTransparency false in
theorem localCocycle_generatorRatios_of_ranges
    (h : ∀ (U : X.Opens) [Nonempty U],
      (D.sectionValueRange U : Set X.functionField) = E.sectionValueRange U) :
    D.localCocycle.GeneratorRatioRegular E.localCocycle := by
  intro i j x hxi hxj
  let U := invertibleOpen D.locallyFree i
  let W := invertibleOpen E.locallyFree j
  let V := U⊓W
  letI : Nonempty U := ⟨⟨i,mem_invertibleOpen D.locallyFree i⟩⟩
  letI : Nonempty W := ⟨⟨j,mem_invertibleOpen E.locallyFree j⟩⟩
  letI : Nonempty V := ⟨⟨x,hxi,hxj⟩⟩
  have hq : D.frameRationalGenerator (invertibleFrame D.locallyFree i)∈E.sectionValueRange V := by
    change D.frameRationalGenerator (invertibleFrame D.locallyFree i) ∈
      (E.sectionValueRange V : Set X.functionField)
    rw [← h V]
    exact ⟨D.frameGenerator (invertibleFrame D.locallyFree i) V inf_le_left,
      D.sectionValue_frameGenerator _ inf_le_left⟩
  obtain ⟨a,ha⟩ := (E.mem_sectionValueRange_iff
    (invertibleFrame E.locallyFree j) (V:=V) inf_le_right _).mp hq
  have hav : X.germToFunctionField V a =
      D.frameRationalGenerator (invertibleFrame D.locallyFree i) /
        E.frameRationalGenerator (invertibleFrame E.locallyFree j) :=
    (eq_div_iff (E.frameRationalGenerator_ne_zero _)).mpr ha
  change D.frameRationalGenerator (invertibleFrame D.locallyFree i) /
    E.frameRationalGenerator (invertibleFrame E.locallyFree j) ∈ regularAtSubring X x
  rw [← hav]
  exact regular_germ_mem_regularAt X V a x ⟨hxi,hxj⟩

/-- Equality of all actual fractional section images gives an actual
sheaf isomorphism preserving the rational embedding. -/
theorem equivalent_of_sectionValueRanges
    (h : ∀ (U : X.Opens) [Nonempty U],
      (D.sectionValueRange U : Set X.functionField) = E.sectionValueRange U) :
    D.Equivalent E := by
  have hCE := D.localCocycle.equivalent_of_generatorRatios E.localCocycle
    (D.localCocycle_generatorRatios_of_ranges E h)
    (E.localCocycle_generatorRatios_of_ranges D (fun U _=>(h U).symm))
  exact D.equivalent_trans E.localCocycle.toCartierData E
    (D.equivalent_trans D.localCocycle.toCartierData E.localCocycle.toCartierData
      D.equivalent_localCocycle hCE)
    (E.equivalent_symm E.localCocycle.toCartierData E.equivalent_localCocycle)

theorem sectionValueRanges_eq_of_cover {ι : Type v} (W : ι→X.Opens)
    (hcover : ∀ x : X,∃ i,x∈W i)
    (hlocal : ∀ i (V : X.Opens) [Nonempty V], V≤W i →
      (D.sectionValueRange V : Set X.functionField)=E.sectionValueRange V)
    (U : X.Opens) [Nonempty U] :
    (D.sectionValueRange U : Set X.functionField)=E.sectionValueRange U := by
  have hincl (D E : CartierData X)
      (hlocal : ∀ i (V : X.Opens) [Nonempty V], V≤W i →
        (D.sectionValueRange V : Set X.functionField)=E.sectionValueRange V) :
      (D.sectionValueRange U : Set X.functionField)⊆E.sectionValueRange U := by
    rintro r ⟨s,rfl⟩
    apply E.exists_section_of_locally_in_range U (D.sectionValue U s)
    intro x
    obtain ⟨i,hxi⟩ := hcover x.val
    let V := U⊓W i
    letI : Nonempty V := ⟨⟨x.val,x.property,hxi⟩⟩
    have hr : D.sectionValue U s∈E.sectionValueRange V := by
      change D.sectionValue U s ∈ (E.sectionValueRange V : Set X.functionField)
      rw [← hlocal i V inf_le_right]
      exact ⟨D.sheaf.presheaf.map (homOfLE inf_le_left).op s,D.sectionValue_restrict _ s⟩
    obtain ⟨t,ht⟩ := hr
    exact ⟨V,inf_le_left,⟨x.property,hxi⟩,t,fun _=>ht⟩
  exact Set.Subset.antisymm (hincl D E hlocal)
    (hincl E D (fun i V _ hV=>(hlocal i V hV).symm))

/-- It suffices to compare the genuine fractional modules locally on an
actual open cover. No abstract divisor-dictionary premise is needed. -/
theorem equivalent_of_local_ranges {ι : Type v} (W : ι→X.Opens)
    (hcover : ∀ x : X,∃ i,x∈W i)
    (hlocal : ∀ i (V : X.Opens) [Nonempty V], V≤W i →
      (D.sectionValueRange V : Set X.functionField)=E.sectionValueRange V) :
    D.Equivalent E :=
  D.equivalent_of_sectionValueRanges E
    (fun U _=>D.sectionValueRanges_eq_of_cover E W hcover hlocal U)

end PaperVerification.ToricSchemes.CartierData

namespace PaperVerification.ToricSchemes.RationalCartierCocycle

variable {X : Scheme.{u}} [IsIntegral X] (C : RationalCartierCocycle X)

/-- The actual section image on a framed open is precisely its principal
fractional module, expressed by division by the genuine generator. -/
theorem mem_sectionValueRange_iff (i : C.index) (V : X.Opens) [Nonempty V]
    (hVi : V≤C.openSet i) (r : X.functionField) :
    r∈C.toCartierData.sectionValueRange V ↔
      r/(C.generator i : X.functionField)∈(X.germToFunctionField V).hom.range := by
  constructor
  · rintro ⟨s,rfl⟩
    exact (C.mem_submodule_iff_local i V hVi s.val).mp s.property
  · intro hr
    let t := (rationalValue X V).symm r
    have ht : t∈C.presheafSubmodule.obj (op V) := by
      apply (C.mem_submodule_iff_local i V hVi t).mpr
      simpa only [t,AddEquiv.apply_symm_apply] using hr
    exact ⟨⟨t,ht⟩,(rationalValue X V).apply_symm_apply r⟩

/-- Equality of the constructed actual Cartier sheaves recovers regular
ratios between the original, possibly differently indexed cocycles. -/
theorem generatorRatios_of_equivalent (D : RationalCartierCocycle X)
    (h : C.toCartierData.Equivalent D.toCartierData) : C.GeneratorRatioRegular D := by
  intro i j x hxi hxj
  let V := C.openSet i⊓D.openSet j
  letI : Nonempty V := ⟨⟨x,hxi,hxj⟩⟩
  have hmem : (C.generator i : X.functionField)∈C.toCartierData.sectionValueRange V := by
    apply (C.mem_sectionValueRange_iff i V inf_le_left _).mpr
    exact ⟨1,by simp⟩
  rw [C.toCartierData.equivalent_sectionValueRange D.toCartierData h V] at hmem
  obtain ⟨a,ha⟩ := (D.mem_sectionValueRange_iff j V inf_le_right _).mp hmem
  rw [← ha]
  exact regular_germ_mem_regularAt X V a x ⟨hxi,hxj⟩

/-- Arithmetic via chosen fractional-sheaf frames agrees with arithmetic
via any genuine original Cartier cocycle presentations. -/
theorem toCartierData_add_equivalent (D : RationalCartierCocycle X) :
    (C.toCartierData.add D.toCartierData).Equivalent (C.mul D).toCartierData := by
  let C' := C.toCartierData.localCocycle
  let D' := D.toCartierData.localCocycle
  have hC : C'.toCartierData.Equivalent C.toCartierData :=
    C.toCartierData.equivalent_symm C'.toCartierData C.toCartierData.equivalent_localCocycle
  have hD : D'.toCartierData.Equivalent D.toCartierData :=
    D.toCartierData.equivalent_symm D'.toCartierData D.toCartierData.equivalent_localCocycle
  exact (C'.mul D').equivalent_of_generatorRatios (C.mul D)
    (GeneratorRatioRegular.mul C' C D' D
      (C'.generatorRatios_of_equivalent C hC) (D'.generatorRatios_of_equivalent D hD))
    (GeneratorRatioRegular.mul C C' D D'
      (C.generatorRatios_of_equivalent C' C.toCartierData.equivalent_localCocycle)
      (D.generatorRatios_of_equivalent D' D.toCartierData.equivalent_localCocycle))

end PaperVerification.ToricSchemes.RationalCartierCocycle

#print axioms PaperVerification.ToricSchemes.CartierData.equivalent_of_local_ranges
end
end Source_ToricCartierRangeEquality
-- END ORIGINAL PaperVerification.ToricCartierRangeEquality



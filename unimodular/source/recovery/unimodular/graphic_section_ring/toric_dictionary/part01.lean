module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.LocalProperties.FinitePresentation
public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.Algebra.Module.Submodule.Equiv

@[expose] public section
set_option autoImplicit false

section
-- BEGIN PaperVerification.ToricRationalSheaf



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
-- END PaperVerification.ToricRationalSheaf
end

section
-- BEGIN PaperVerification.ToricCartierSheaf



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
-- END PaperVerification.ToricCartierSheaf
end

section
-- BEGIN PaperVerification.ToricInvertibleAffine



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
-- END PaperVerification.ToricInvertibleAffine
end

section
-- BEGIN PaperVerification.ToricLocallyInvertible



/-!
# Actual rank-one local frames imply module invertibility

Local rank-one trivializations first imply finite presentation. Localization
then commutes with the dual and tensor product, carrying the canonical
evaluation pairing to its local counterpart. Its local bijectivity proves
global bijectivity. Neither finite generation nor projectivity nor a
global trivialization is an extra input.
-/

noncomputable section

namespace PaperVerification.ToricSchemes

open Module TensorProduct
open scoped TensorProduct

section OneLocalization

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]
  (S : Submonoid R) (A : Type*) [CommRing A] [Algebra R A]
  [IsLocalization S A] [Module A N] [IsScalarTower R A N]
  (f : M →ₗ[R] N) [IsLocalizedModule S f]

/-- Localization of actual linear functionals, with scalars extended
to the localized ring. -/
def localizedDual : Dual R M →ₗ[R] Dual A N :=
  IsLocalizedModule.mapExtendScalars S f (Algebra.linearMap R A) A

@[simp] theorem localizedDual_apply (φ : Dual R M) (m : M) :
    localizedDual S A f φ (f m) = algebraMap R A (φ m) := by
  exact IsLocalizedModule.map_apply S f (Algebra.linearMap R A) φ m

instance localizedDual_isLocalized [Module.FinitePresentation R M] :
    IsLocalizedModule S (localizedDual S A f) := by
  dsimp only [localizedDual]
  infer_instance

/-- The actual localization map on the domain of the evaluation
pairing. The tensor product in the codomain is over the localized ring. -/
def localizedEvaluationDomainMap :
    Dual R M ⊗[R] M →ₗ[R] Dual A N ⊗[A] N :=
  ((IsLocalization.moduleTensorEquiv S A (Dual A N) N).symm.restrictScalars R).toLinearMap.comp
    (TensorProduct.map (localizedDual S A f) f)

@[simp] theorem localizedEvaluationDomainMap_tmul (φ : Dual R M) (m : M) :
    localizedEvaluationDomainMap S A f (φ ⊗ₜ[R] m) =
      localizedDual S A f φ ⊗ₜ[A] f m := rfl

instance localizedEvaluationDomainMap_isLocalized [Module.FinitePresentation R M] :
    IsLocalizedModule S (localizedEvaluationDomainMap S A f) := by
  exact IsLocalizedModule.of_linearEquiv S
    (TensorProduct.map (localizedDual S A f) f)
    ((IsLocalization.moduleTensorEquiv S A (Dual A N) N).symm.restrictScalars R)

/-- The evaluation pairing commutes with the genuine localization maps. -/
theorem contractLeft_localization [Module.FinitePresentation R M] :
    IsLocalizedModule.map S (localizedEvaluationDomainMap S A f)
        (Algebra.linearMap R A) (contractLeft R M) =
      (contractLeft A N).restrictScalars R := by
  apply IsLocalizedModule.linearMap_ext S (localizedEvaluationDomainMap S A f)
    (Algebra.linearMap R A)
  apply TensorProduct.ext'
  intro φ m
  simpa only [LinearMap.comp_apply, contractLeft_apply, Algebra.linearMap_apply,
    LinearMap.restrictScalars_apply, localizedEvaluationDomainMap_tmul, localizedDual_apply] using
    IsLocalizedModule.map_apply S (localizedEvaluationDomainMap S A f)
      (Algebra.linearMap R A) (contractLeft R M) (φ ⊗ₜ[R] m)

end OneLocalization

section PrincipalCover

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (s : Set R) (hs : Ideal.span s = ⊤)
  (A : s → Type*) [∀ r, CommRing (A r)] [∀ r, Algebra R (A r)]
  [∀ r : s, IsLocalization.Away r.val (A r)]
  (N : s → Type*) [∀ r, AddCommGroup (N r)] [∀ r, Module R (N r)]
  [∀ r, Module (A r) (N r)] [∀ r, IsScalarTower R (A r) (N r)]
  (f : ∀ r, M →ₗ[R] N r) [∀ r : s, IsLocalizedModule.Away r.val (f r)]

include hs f in
/-- A module with actual rank-one frames on a principal-open cover is
invertible in the tensor-product sense used by Mathlib's Picard group.
The cover need not be presented as finite: finite presentation is derived
from the unit-ideal cover by the local-property theorem. -/
theorem invertible_of_principalCover_rankOne
    (hframe : ∀ r : s, Nonempty (N r ≃ₗ[A r] A r)) :
    Module.Invertible R M := by
  classical
  let e (r : s) : N r ≃ₗ[A r] A r := Classical.choice (hframe r)
  letI (r : s) : Module.FinitePresentation (A r) (N r) :=
    Module.FinitePresentation.of_equiv (e r).symm
  letI : Module.FinitePresentation R M :=
    Module.FinitePresentation.of_localizationSpan' (Rₚ := A) s hs f (fun r => inferInstance)
  letI (r : s) : Module.Invertible (A r) (N r) :=
    Module.Invertible.congr (e r).symm
  refine ⟨?_⟩
  apply bijective_of_isLocalized_span s hs
    (fun r => Dual (A r) (N r) ⊗[A r] N r)
    (fun r => localizedEvaluationDomainMap (Submonoid.powers r.val) (A r) (f r))
    A (fun r => Algebra.linearMap R (A r)) (contractLeft R M)
  intro r
  rw [contractLeft_localization]
  exact Module.Invertible.bijective

include hs in
/-- Specialization to the canonical localized ring and module, without
requiring any identifications as extra structure. -/
theorem invertible_of_localizationCover_rankOne
    (hframe : ∀ r : s, Nonempty
      (LocalizedModule.Away r.val M ≃ₗ[Localization.Away r.val] Localization.Away r.val)) :
    Module.Invertible R M :=
  invertible_of_principalCover_rankOne s hs
    (fun r => Localization.Away r.val) (fun r => LocalizedModule.Away r.val M)
    (fun r => LocalizedModule.mkLinearMap (Submonoid.powers r.val) M) hframe

end PrincipalCover

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.invertible_of_principalCover_rankOne
end
-- END PaperVerification.ToricLocallyInvertible
end

section
-- BEGIN PaperVerification.ToricLaurentPicard



/-!
# The actual split-torus coordinate ring has trivial Picard group

The group algebra of Z^n is identified, recursively and explicitly, with
an iterated Laurent polynomial ring. Polynomial unique factorization and
localization preserve unique factorization. Mathlib's class-group/Picard
equivalence then trivializes every actual invertible module over this ring.
The passage from invertible sheaves on its spectrum to modules is separate.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open scoped Polynomial nonZeroDivisors

def latticeSuccCoordinates (n : ℕ) :
    (Fin (n + 1) → ℤ) ≃+ ℤ × (Fin n → ℤ) where
  toFun x := (x 0, fun i => x i.succ)
  invFun x := Fin.cons x.1 x.2
  left_inv x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv x := by
    apply Prod.ext
    · rfl
    · funext i
      rfl
  map_add' _ _ := rfl

abbrev torusCoordinateRing (k : Type*) [CommRing k] (n : ℕ) :=
  AddMonoidAlgebra k (Fin n → ℤ)

variable (k : Type*) [Field k]

/-- Separating the first character coordinate gives an actual algebra
equivalence with a one-variable Laurent extension of the smaller torus. -/
def torusCoordinateRingSucc (n : ℕ) :
    torusCoordinateRing k (n + 1) ≃ₐ[k]
      AddMonoidAlgebra (torusCoordinateRing k n) ℤ :=
  (AddMonoidAlgebra.domCongr k k (latticeSuccCoordinates n)).trans
    (AddMonoidAlgebra.curryAlgEquiv k)

theorem torusCoordinateRing_isDomain (n : ℕ) : IsDomain (torusCoordinateRing k n) := by
  induction n with
  | zero =>
      exact MulEquiv.isDomain k
        (AddMonoidAlgebra.uniqueAlgEquiv k (Fin 0 → ℤ)).toMulEquiv
  | succ n ih =>
      letI := ih
      exact MulEquiv.isDomain (AddMonoidAlgebra (torusCoordinateRing k n) ℤ)
        (torusCoordinateRingSucc k n).toMulEquiv

/-- Laurent extension preserves unique factorization by its literal
localization presentation at powers of the polynomial variable. -/
theorem laurent_uniqueFactorization (A : Type*) [CommRing A] [IsDomain A]
    [UniqueFactorizationMonoid A] : UniqueFactorizationMonoid (AddMonoidAlgebra A ℤ) :=
  UniqueFactorizationMonoid.of_isLocalization
    (Submonoid.powers (Polynomial.X : Polynomial A)) (AddMonoidAlgebra A ℤ)

theorem torusCoordinateRing_uniqueFactorization (n : ℕ) :
    UniqueFactorizationMonoid (torusCoordinateRing k n) := by
  induction n with
  | zero =>
      exact ((AddMonoidAlgebra.uniqueAlgEquiv k (Fin 0 → ℤ)).symm.toMulEquiv).uniqueFactorizationMonoid
        inferInstance
  | succ n ih =>
      letI := ih
      letI := torusCoordinateRing_isDomain k n
      letI := laurent_uniqueFactorization (torusCoordinateRing k n)
      exact ((torusCoordinateRingSucc k n).symm.toMulEquiv).uniqueFactorizationMonoid inferInstance

/-- The Picard group here is Mathlib's actual group of invertible
modules under tensor product, not a fan-defined substitute. -/
theorem torusPic_subsingleton (n : ℕ) :
    Subsingleton (CommRing.Pic (torusCoordinateRing k n)) := by
  letI := torusCoordinateRing_isDomain k n
  letI := torusCoordinateRing_uniqueFactorization k n
  infer_instance

/-- Every invertible module over the actual split-torus coordinate
ring admits a global rank-one trivialization. -/
def torusInvertibleModuleEquiv (n : ℕ) (V : Type*)
    [AddCommGroup V] [Module (torusCoordinateRing k n) V]
    [Module.Invertible (torusCoordinateRing k n) V] :
    V ≃ₗ[torusCoordinateRing k n] torusCoordinateRing k n := by
  letI := torusPic_subsingleton k n
  exact Classical.choice (Module.Invertible.free_iff_linearEquiv.mp inferInstance)

theorem torusFractionalIdeal_principal (n : ℕ)
    (I : FractionalIdeal (torusCoordinateRing k n)⁰
      (FractionRing (torusCoordinateRing k n))) (hI : IsUnit I) :
    (I : Submodule (torusCoordinateRing k n) (FractionRing (torusCoordinateRing k n))).IsPrincipal := by
  letI := torusCoordinateRing_isDomain k n
  letI := torusCoordinateRing_uniqueFactorization k n
  exact ClassGroup.isPrincipal_coeSubmodule_of_isUnit I hI

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.torusCoordinateRing_uniqueFactorization
#print axioms PaperVerification.ToricCharacters.torusInvertibleModuleEquiv
end
-- END PaperVerification.ToricLaurentPicard
end

section
-- BEGIN PaperVerification.ToricAffinePicard



/-!
# Invertible sheaves on an affine scheme and triviality on the split torus

Actual local frames make the section module locally rank one. The literal
principal-open restriction maps are module localizations by quasi-coherence.
The local algebra criterion therefore makes the global section module
invertible, and the tilde equivalence transports a module trivialization
back to an actual sheaf trivialization. Applied to the Laurent coordinate
ring, this proves that every actual invertible sheaf on the split torus is
trivial, with no affine Picard correspondence assumed.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace PaperVerification.ToricSchemes

variable {R : CommRingCat.{u}} (M : (Spec R).Modules)

/-- Principal opens subordinate to one of the actual local frames. -/
def framedPrincipalSet (hM : IsInvertibleModule M) : Set R :=
  {f | ∃ x : Spec R,PrimeSpectrum.basicOpen f≤ invertibleOpen hM x}

theorem framedPrincipalSet_span (hM : IsInvertibleModule M) :
    Ideal.span (framedPrincipalSet M hM)=⊤ := by
  apply PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mp
  apply le_antisymm le_top
  intro x hx
  obtain ⟨f,hxf,hf⟩ := exists_basicOpen_frame M hM x
  exact Opens.mem_iSup.mpr ⟨f,Opens.mem_iSup.mpr ⟨⟨x,hf⟩,hxf⟩⟩

set_option maxHeartbeats 2000000 in
/-- The global section module of an actual invertible sheaf is invertible in
Mathlib's tensor-product sense. All finiteness is derived from local frames. -/
theorem invertibleModule_globalSections (hM : IsInvertibleModule M) :
    Module.Invertible R Γ(M,⊤) := by
  classical
  let G : ModuleCat.{u} R := (modulesSpecToSheaf.obj M).obj.obj (op ⊤)
  change Module.Invertible R G
  let s := framedPrincipalSet M hM
  let U (f : s) : (Spec R).Opens := PrimeSpectrum.basicOpen f.val
  let A (f : s) : Type u := Γ(Spec R,U f)
  let N (f : s) : ModuleCat.{u} R := (modulesSpecToSheaf.obj M).obj.obj (op (U f))
  letI (f : s) : Algebra R (A f) := StructureSheaf.openAlgebra R (op (U f))
  letI (f : s) : IsLocalization.Away f.val (A f) :=
    StructureSheaf.IsLocalization.to_basicOpen R f.val
  letI (f : s) : Module (A f) (N f) := (M.val.obj (op (U f))).isModule
  letI (f : s) : IsScalarTower R (A f) (N f) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let ρ (f : s) : G →ₗ[R] N f :=
    ((modulesSpecToSheaf.obj M).obj.map
      (homOfLE (show U f ≤ (⊤ : (Spec R).Opens) from le_top)).op).hom
  letI (f : s) : IsLocalizedModule.Away f.val (ρ f) :=
    invertibleAffine_isLocalizing M hM f.val
  apply invertible_of_principalCover_rankOne s (framedPrincipalSet_span M hM)
    A (fun f => (N f : Type u)) ρ
  intro f
  obtain ⟨x,hx⟩ := f.property
  exact ⟨invertibleFrameCoordinates hM x (U f) hx⟩

/-- Triviality of the actual ring Picard group trivializes actual invertible
sheaves on its spectrum. This is derived through the affine equivalence. -/
def affineInvertibleSheafIso [Subsingleton (CommRing.Pic R)]
    (hM : IsInvertibleModule M) :
    M ≅ SheafOfModules.unit (Spec R).ringCatSheaf := by
  letI := invertibleModule_globalSections M hM
  let e : Γ(M,⊤) ≃ₗ[R] R :=
    Classical.choice (Module.Invertible.free_iff_linearEquiv.mp inferInstance)
  exact (invertibleAffineTildeIso M hM).symm ≪≫
    (tilde.functor R).mapIso e.toModuleIso ≪≫ tildeSelf

section Torus

variable (k : Type u) [Field k] (n : ℕ)

/-- Every actual invertible sheaf on the split torus is globally rank one. -/
def torusInvertibleSheafIso
    (M : (Spec (CommRingCat.of (ToricCharacters.torusCoordinateRing k n))).Modules)
    (hM : IsInvertibleModule M) :
    M ≅ SheafOfModules.unit
      (Spec (CommRingCat.of (ToricCharacters.torusCoordinateRing k n))).ringCatSheaf := by
  letI := ToricCharacters.torusPic_subsingleton k n
  exact affineInvertibleSheafIso M hM

end Torus

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.invertibleModule_globalSections
#print axioms PaperVerification.ToricSchemes.torusInvertibleSheafIso
end
-- END PaperVerification.ToricAffinePicard
end

section
-- BEGIN PaperVerification.ToricRegularRational



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
-- END PaperVerification.ToricRegularRational
end

section
-- BEGIN PaperVerification.ToricCartierCocycle



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
-- END PaperVerification.ToricCartierCocycle
end

section
-- BEGIN PaperVerification.ToricCartierPresentation



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
-- END PaperVerification.ToricCartierPresentation
end

#eval "TORIC_DICTIONARY_PART_01_EOF"

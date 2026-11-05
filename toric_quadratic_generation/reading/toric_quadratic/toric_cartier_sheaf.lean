module

public import PaperVerification.ToricRationalSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

@[expose] public section

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

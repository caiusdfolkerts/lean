module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.Algebra.Category.Ring.Constructions

@[expose] public section

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

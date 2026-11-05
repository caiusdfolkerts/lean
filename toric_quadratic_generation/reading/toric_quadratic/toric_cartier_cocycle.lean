module

public import PaperVerification.ToricCartierSheaf
public import PaperVerification.ToricRegularRational
public import Mathlib.Algebra.Module.Submodule.Equiv

@[expose] public section

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

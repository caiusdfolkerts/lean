module

public import Mathlib.CategoryTheory.NatIso

/-! # Retaining a specified isomorphism without repeatedly unfolding its data

Choosing from the proved singleton containing an already constructed
isomorphism gives literally that same isomorphism. The equality below
retains the original hom and inverse maps. This is only a normalization
boundary for large geometric functor isomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace ToricPower

universe u v
variable {C : Type u} [Category.{v} C] {X Y : C}

/-- The original isomorphism, selected from its proved singleton. -/
def specifiedIso (e : X ≅ Y) : X ≅ Y :=
  Classical.choose (show ∃ e' : X ≅ Y, e' = e from ⟨e, rfl⟩)

/-- Literal equality to the original isomorphism, including both maps. -/
theorem specifiedIso_eq (e : X ≅ Y) : specifiedIso e = e :=
  Classical.choose_spec (show ∃ e' : X ≅ Y, e' = e from ⟨e, rfl⟩)

/-- Retain an entire dependent family as a specified function. Evaluating
this family does not unfold the construction of any component. -/
def specifiedFunction {α : Sort*} {β : α → Sort*} (f : ∀ x, β x) : ∀ x, β x :=
  Classical.choose (show ∃ f' : ∀ x, β x, f' = f from ⟨f, rfl⟩)

theorem specifiedFunction_eq {α : Sort*} {β : α → Sort*} (f : ∀ x, β x) :
    specifiedFunction f = f :=
  Classical.choose_spec (show ∃ f' : ∀ x, β x, f' = f from ⟨f, rfl⟩)

section FunctorEvaluation
variable {D : Type*} [Category D] {F G : C ⥤ D}

/-- The specified component, with the original component retained by equality. -/
def specifiedIsoAt (e : F ≅ G) (X : C) : F.obj X ≅ G.obj X :=
  specifiedIso (e.app X)

theorem specifiedIsoAt_eq (e : F ≅ G) (X : C) :
    specifiedIsoAt e X = e.app X := specifiedIso_eq _

end FunctorEvaluation

/-- Compose specified isomorphisms without exposing their structures. -/
def specifiedIsoTrans {Z : C} (e : X ≅ Y) (f : Y ≅ Z) : X ≅ Z :=
  specifiedIso (e ≪≫ f)

theorem specifiedIsoTrans_eq {Z : C} (e : X ≅ Y) (f : Y ≅ Z) :
    specifiedIsoTrans e f = e ≪≫ f := specifiedIso_eq _

end ToricPower

end

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

/-!
# Restricting an actual group action to an invariant open

An equality of inverse-image opens under the action and projection lets the
action factor through the open subscheme. Its unit and associativity laws
follow by cancelling the open immersion. Thus the restricted object carries
an actual action on all test schemes, and its inclusion is equivariant.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj

namespace CategoryTheory.ModObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (G : C) [MonObj G] {X Y : C} [ModObj G X]

/-- A factor of an action through a monomorphism satisfies the action laws. -/
@[instance_reducible]
def ofMono (i : Y ⟶ X) [Mono i] (a : G ⊗ Y ⟶ Y)
    (ha : a ≫ i = G ◁ i ≫ γ[G,X]) : ModObj G Y where
  smul := a
  one_smul := by
    change (η[G] ▷ Y) ≫ a = (λ_ Y).hom
    apply (cancel_mono i).mp
    simp only [Category.assoc, ha]
    rw [← whisker_exchange_assoc, ModObj.one_smul_self, leftUnitor_naturality]
  mul_smul := by
    change (μ[G] ▷ Y) ≫ a = (α_ G G Y).hom ≫ (G ◁ a) ≫ a
    apply (cancel_mono i).mp
    simp only [Category.assoc, ha]
    rw [← whiskerLeft_comp_assoc, ha, whiskerLeft_comp,
      ← whisker_exchange_assoc, ModObj.mul_smul_self,
      associator_naturality_right_assoc]
    simp only [Category.assoc]

end CategoryTheory.ModObj

namespace AlgebraicGeometry.GroupAction

variable {S : Scheme.{u}} (X : Over S)

/-- The actual open subscheme with its inherited structure morphism. -/
abbrev openOver (U : X.left.Opens) : Over S := Over.mk (U.ι ≫ X.hom)

/-- Its actual inclusion over the base. -/
abbrev openInclusion (U : X.left.Opens) : openOver X U ⟶ X :=
  Over.homMk U.ι

/-- Factor a morphism over the base through an open containing its image. -/
def openLift (U : X.left.Opens) {Z : Over S} (f : Z ⟶ X)
    (hf : Set.range f.left ⊆ (U : Set X.left)) : Z ⟶ openOver X U :=
  Over.homMk
    (IsOpenImmersion.lift U.ι f.left (fun x hx => ⟨⟨x, hf hx⟩, rfl⟩))
    (by
      change _ ≫ (U.ι ≫ X.hom) = Z.hom
      rw [← Category.assoc, IsOpenImmersion.lift_fac]
      exact f.w)

@[reassoc (attr := simp)]
theorem openLift_inclusion (U : X.left.Opens) {Z : Over S} (f : Z ⟶ X)
    (hf : Set.range f.left ⊆ (U : Set X.left)) :
    openLift X U f hf ≫ openInclusion X U = f := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac _ _ _

variable (G : Over S) [MonObj G] [ModObj G X]
    (U : X.left.Opens)
    (hU : (γ[G,X]).left ⁻¹ᵁ U = (snd G X).left ⁻¹ᵁ U)

include hU

/-- Invariance puts the whole action image of `G × U` inside `U`. -/
theorem restrictedAction_range :
    Set.range ((G ◁ openInclusion X U) ≫ γ[G,X]).left ⊆ (U : Set X.left) := by
  rintro x ⟨z, rfl⟩
  have hp : (snd G X).left ((G ◁ openInclusion X U).left z) ∈ U := by
    have he := congrArg (fun f : G ⊗ openOver X U ⟶ X => f.left z)
      (whiskerLeft_snd G (openInclusion X U))
    change (snd G X).left ((G ◁ openInclusion X U).left z) =
      U.ι ((snd G (openOver X U)).left z) at he
    rw [he]
    exact ((snd G (openOver X U)).left z).property
  exact (Set.ext_iff.mp (congrArg SetLike.coe hU)
    ((G ◁ openInclusion X U).left z)).mpr hp

/-- The restricted action map, obtained by the open immersion's universal
property rather than by choosing pointwise actions. -/
def restrictedAction : G ⊗ openOver X U ⟶ openOver X U :=
  openLift X U ((G ◁ openInclusion X U) ≫ γ[G,X])
    (restrictedAction_range X G U hU)

@[reassoc (attr := simp)]
theorem restrictedAction_inclusion :
    restrictedAction X G U hU ≫ openInclusion X U =
      (G ◁ openInclusion X U) ≫ γ[G,X] :=
  openLift_inclusion X U _ _

/-- An invariant open subscheme inherits an actual monoid-scheme action. -/
@[instance_reducible]
def restrictedModObj : ModObj G (openOver X U) :=
  ModObj.ofMono G (openInclusion X U) (restrictedAction X G U hU)
    (restrictedAction_inclusion X G U hU)

/-- The inclusion of the invariant open is genuinely equivariant. -/
theorem openInclusion_isModHom :
    letI := restrictedModObj X G U hU
    IsModHom G (openInclusion X U) := by
  letI := restrictedModObj X G U hU
  exact ⟨restrictedAction_inclusion X G U hU⟩

end AlgebraicGeometry.GroupAction

#print axioms AlgebraicGeometry.GroupAction.restrictedModObj
#print axioms AlgebraicGeometry.GroupAction.openInclusion_isModHom

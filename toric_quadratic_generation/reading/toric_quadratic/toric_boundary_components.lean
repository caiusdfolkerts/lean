module

public import PaperVerification.ToricIntrinsicAction
public import PaperVerification.ToricTorusGeometricIntegral
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

@[expose] public section

/-!
# Actual invariance of the irreducible boundary components

The torus projection has geometrically irreducible fibres, so the
preimage of an irreducible component is irreducible. Its image under the
action lies in the boundary and contains the original component by the
unit section. Maximality forces equality. This argument takes place on
the genuine scheme product and works over finite fields as well.
-/

noncomputable section

universe u v

namespace CategoryTheory

open MonoidalCategory CartesianMonoidalCategory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- Base change along a product projection, with the literal chosen
cartesian tensor product. -/
theorem isPullback_whiskerLeft_snd (G : C) {X Y : C} (f : Y ⟶ X) :
    IsPullback (G ◁ f) (snd G Y) (snd G X) f := by
  refine IsPullback.mk' (by simp) ?_ ?_
  · intro Z a b hab hsnd
    apply CartesianMonoidalCategory.hom_ext
    · have h := congrArg (fun z => z ≫ fst G X) hab
      simpa only [Category.assoc, whiskerLeft_fst, Category.comp_id] using h
    · exact hsnd
  · intro Z a b hab
    refine ⟨lift (a ≫ fst G X) b, ?_, by simp⟩
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · simpa only [Category.assoc, whiskerLeft_snd, lift_snd_assoc] using hab.symm

end CategoryTheory

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory MonObj

/-- Maximal irreducibility inside the actual boundary, without a chosen
fan or a description by invariant coordinate divisors. -/
def IsBoundaryComponent {X : Type*} [TopologicalSpace X]
    (B Z : Set X) : Prop :=
  Maximal (fun W : Set X => IsIrreducible W ∧ W ⊆ B) Z

/-- An irreducible family inside a boundary that contains one whole
irreducible component must remain in that component. -/
theorem boundaryComponent_image_eq
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {B Z : Set X} (hZ : IsBoundaryComponent B Z)
    (p a : Y → X) (e : X → Y)
    (ha : Continuous a) (hpZ : IsIrreducible (p ⁻¹' Z))
    (hB : ∀ y, p y ∈ B → a y ∈ B)
    (hp : ∀ x, p (e x)=x) (he : ∀ x, a (e x)=x) :
    a '' (p ⁻¹' Z)=Z := by
  have hsub : Z ⊆ a '' (p ⁻¹' Z) := by
    intro x hx
    exact ⟨e x,by simpa only [Set.mem_preimage,hp] using hx,he x⟩
  apply Set.Subset.antisymm _ hsub
  exact hZ.2 ⟨hpZ.image a ha.continuousOn,by
    rintro x ⟨y,hy,rfl⟩
    exact hB y (hZ.1.2 hy)⟩ hsub

/-- An open-immersion pullback identifies its actual open image. -/
theorem opensRange_of_isPullback {P A B X : Scheme.{u}}
    {f : P ⟶ A} {g : P ⟶ B} {a : A ⟶ X} {j : B ⟶ X}
    (h : IsPullback f g a j) [IsOpenImmersion j] :
    letI : IsOpenImmersion f := MorphismProperty.of_isPullback h.flip inferInstance
    f.opensRange = a ⁻¹ᵁ j.opensRange := by
  letI : IsOpenImmersion f := MorphismProperty.of_isPullback h.flip inferInstance
  have he := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback h.flip
    (⊤ : B.Opens)
  simpa only [Scheme.Hom.preimage_top,Scheme.Hom.image_top_eq_opensRange] using he

variable (k : Type u) [Field k] (n : ℕ)
    (X : Over (Spec (CommRingCat.of k)))
    [ModObj (splitTorusOver k (Fin n → ℤ)) X]

namespace SplitToricEmbedding

variable {k n X} (T : SplitToricEmbedding k n X)

/-- The action and projection have exactly the same inverse image of the
actual dense torus open. This uses the genuine action pullback square. -/
theorem action_preimage_torusOpen :
    (γ[splitTorusOver k (Fin n → ℤ),X]).left ⁻¹ᵁ T.torusOpen =
      (snd (splitTorusOver k (Fin n → ℤ)) X).left ⁻¹ᵁ T.torusOpen := by
  letI : IsOpenImmersion ((Over.forget (Spec (CommRingCat.of k))).map T.torus) :=
    T.open_immersion
  have ha := (T.torus_action_isPullback).map (Over.forget (Spec (CommRingCat.of k)))
  have hp := (isPullback_whiskerLeft_snd (splitTorusOver k (Fin n → ℤ)) T.torus).map
    (Over.forget (Spec (CommRingCat.of k)))
  exact (opensRange_of_isPullback ha).symm.trans (opensRange_of_isPullback hp)

theorem action_preimage_boundary :
    (γ[splitTorusOver k (Fin n → ℤ),X]).left ⁻¹' T.boundary =
      (snd (splitTorusOver k (Fin n → ℤ)) X).left ⁻¹' T.boundary := by
  have h := congrArg (fun U : (splitTorusOver k (Fin n → ℤ) ⊗ X).left.Opens =>
    (U : Set (splitTorusOver k (Fin n → ℤ) ⊗ X).left)ᶜ)
    T.action_preimage_torusOpen
  exact h

/-- Every actual irreducible boundary component is invariant under the
whole group scheme action. No rational-point density is used. -/
theorem boundaryComponent_invariant {Z : Set X.left}
    (hZ : IsBoundaryComponent T.boundary Z) :
    (γ[splitTorusOver k (Fin n → ℤ),X]).left ''
        ((snd (splitTorusOver k (Fin n → ℤ)) X).left ⁻¹' Z) = Z := by
  let G := splitTorusOver k (Fin n → ℤ)
  let e : X ⟶ G ⊗ X := lift (1 : X ⟶ G) (𝟙 X)
  have hp : e ≫ snd G X = 𝟙 X := by simp only [e,lift_snd]
  have ha : e ≫ γ[G,X] = 𝟙 X := by
    change (1 : X ⟶ G) • (𝟙 X) = 𝟙 X
    exact one_smul _ _
  apply boundaryComponent_image_eq hZ
    (snd G X).left (γ[G,X]).left e.left (γ[G,X]).left.continuous
    (torusProjection_isIrreducible_preimage k n X hZ.1.1)
  · intro y hy
    change y ∈ (γ[G,X]).left ⁻¹' T.boundary
    rw [T.action_preimage_boundary]
    exact hy
  · intro x
    exact congrArg (fun f : X ⟶ X => f.left x) hp
  · intro x
    exact congrArg (fun f : X ⟶ X => f.left x) ha

end SplitToricEmbedding

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.boundaryComponent_invariant

module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Saturation under an actual group-scheme action

The action saturation of a subset is invariant on the scheme product.
The proof uses categorical pullbacks and the surjectivity of the map from
the points of a scheme pullback to the set-theoretic fiber product. It makes
no assumption that rational points of the group are dense.

This is a local preparation for toric affine neighborhoods. It does not
assert that the saturation of an affine open is affine or quasi-projective.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace CategoryTheory.ModObj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    (G X : C) [GrpObj G] [ModObj G X]

/-- Composition of two action arrows: `(g, (h, x)) ↦ (gh, x)`. -/
def orbitComposition : G ⊗ (G ⊗ X) ⟶ G ⊗ X :=
  lift (fst G (G ⊗ X) * (snd G (G ⊗ X) ≫ fst G X))
    (snd G (G ⊗ X) ≫ snd G X)

@[reassoc (attr := simp)] theorem orbitComposition_fst :
    orbitComposition G X ≫ fst G X =
      fst G (G ⊗ X) * (snd G (G ⊗ X) ≫ fst G X) := by
  simp [orbitComposition]

@[reassoc (attr := simp)] theorem orbitComposition_snd :
    orbitComposition G X ≫ snd G X = snd G (G ⊗ X) ≫ snd G X := by
  simp [orbitComposition]

/-- The action groupoid composition square is a categorical pullback. -/
theorem orbitComposition_isPullback :
    IsPullback (orbitComposition G X) (G ◁ γ[G, X]) γ[G, X] γ[G, X] := by
  refine IsPullback.mk' ?_ ?_ ?_
  · calc
      orbitComposition G X ≫ γ[G, X] =
          (fst G (G ⊗ X) * (snd G (G ⊗ X) ≫ fst G X)) •
            (snd G (G ⊗ X) ≫ snd G X) := rfl
      _ = fst G (G ⊗ X) •
          ((snd G (G ⊗ X) ≫ fst G X) • (snd G (G ⊗ X) ≫ snd G X)) :=
        SemigroupAction.mul_smul _ _ _
      _ = (G ◁ γ[G, X]) ≫ γ[G, X] := by
        rw [Hom.smul_def]
        congr 1
        apply CartesianMonoidalCategory.hom_ext
        · simp
        · simp only [lift_snd, whiskerLeft_snd, Hom.smul_def,
            ← comp_lift_assoc, lift_fst_snd, Category.id_comp] <;> rfl
  · intro Z a b ha hb
    have ho : a ≫ fst G (G ⊗ X) = b ≫ fst G (G ⊗ X) := by
      simpa only [Category.assoc, whiskerLeft_fst, Category.comp_id] using
        congrArg (fun f => f ≫ fst G X) hb
    have hm : (a ≫ fst G (G ⊗ X)) * (a ≫ snd G (G ⊗ X) ≫ fst G X) =
        (b ≫ fst G (G ⊗ X)) * (b ≫ snd G (G ⊗ X) ≫ fst G X) := by
      simpa only [Category.assoc, orbitComposition_fst, MonObj.comp_mul] using
        congrArg (fun f => f ≫ fst G X) ha
    rw [ho] at hm
    apply CartesianMonoidalCategory.hom_ext
    · exact ho
    · apply CartesianMonoidalCategory.hom_ext
      · have hm' := _root_.mul_left_cancel hm
        simpa only [Category.assoc] using hm'
      · simpa only [Category.assoc, orbitComposition_snd] using
          congrArg (fun f => f ≫ snd G X) ha
  · intro Z a b hab
    let g : Z ⟶ G := b ≫ fst G X
    let h : Z ⟶ G := a ≫ fst G X
    let x : Z ⟶ X := a ≫ snd G X
    let y : Z ⟶ X := b ≫ snd G X
    have hxy : h • x = g • y := by
      simpa only [h, x, g, y, Hom.smul_def, ← comp_lift_assoc,
        lift_fst_snd, Category.id_comp] using hab
    refine ⟨lift g (lift (g⁻¹ * h) x), ?_, ?_⟩
    · apply CartesianMonoidalCategory.hom_ext
      · simp [orbitComposition, MonObj.comp_mul, h]
      · simp [orbitComposition, x]
    · apply CartesianMonoidalCategory.hom_ext
      · simp [g]
      · simp only [Category.assoc, whiskerLeft_snd, lift_snd_assoc]
        change (g⁻¹ * h) • x = y
        rw [SemigroupAction.mul_smul, hxy, _root_.inv_smul_smul]

/-- The projection/action square obtained by base change along a product. -/
theorem orbitProjection_isPullback :
    IsPullback (snd G (G ⊗ X)) (G ◁ γ[G, X]) γ[G, X] (snd G X) := by
  refine IsPullback.mk' (by simp) ?_ ?_
  · intro Z a b ha hb
    apply CartesianMonoidalCategory.hom_ext
    · simpa only [Category.assoc, whiskerLeft_fst, Category.comp_id] using
        congrArg (fun f => f ≫ fst G X) hb
    · exact ha
  · intro Z a b hab
    refine ⟨lift (b ≫ fst G X) a, by simp, ?_⟩
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · simpa only [Category.assoc, whiskerLeft_snd, lift_snd_assoc] using hab

end CategoryTheory.ModObj

namespace AlgebraicGeometry.GroupAction

variable {S : Scheme.{u}} (G X : Over S) [GrpObj G] [ModObj G X]

/-- Saturation by the whole group scheme, using the actual product points. -/
def saturation (U : Set X.left) : Set X.left :=
  (γ[G, X]).left '' ((snd G X).left ⁻¹' U)

theorem subset_saturation (U : Set X.left) : U ⊆ saturation G X U := by
  intro x hx
  let e : X ⟶ G ⊗ X := lift (1 : X ⟶ G) (𝟙 X)
  have hp : e ≫ snd G X = 𝟙 X := by simp [e]
  have ha : e ≫ γ[G, X] = 𝟙 X := by
    change (1 : X ⟶ G) • (𝟙 X) = 𝟙 X
    exact one_smul _ _
  refine ⟨e.left x, ?_, ?_⟩
  · change (snd G X).left (e.left x) ∈ U
    have hpx : (snd G X).left (e.left x) = x :=
      congrArg (fun f : X ⟶ X => f.left x) hp
    rwa [hpx]
  · exact congrArg (fun f : X ⟶ X => f.left x) ha

/-- Saturation is invariant as a subset of the actual scheme product. -/
theorem action_preimage_saturation (U : Set X.left) :
    (γ[G, X]).left ⁻¹' saturation G X U =
      (snd G X).left ⁻¹' saturation G X U := by
  have ha := (ModObj.orbitComposition_isPullback G X).map (Over.forget S)
  have hp := (ModObj.orbitProjection_isPullback G X).map (Over.forget S)
  have h₁ := Scheme.image_preimage_eq_of_isPullback ha ((snd G X).left ⁻¹' U)
  have h₂ := Scheme.image_preimage_eq_of_isPullback hp ((snd G X).left ⁻¹' U)
  simp only [Over.forget_map] at h₁ h₂
  change (γ[G, X]).left ⁻¹' ((γ[G, X]).left '' ((snd G X).left ⁻¹' U)) =
    (snd G X).left ⁻¹' ((γ[G, X]).left '' ((snd G X).left ⁻¹' U))
  refine h₁.symm.trans (Eq.trans ?_ h₂)
  congr 1
  ext z
  change (snd G X).left ((ModObj.orbitComposition G X).left z) ∈ U ↔
    (snd G X).left ((snd G (G ⊗ X)).left z) ∈ U
  have he := congrArg (fun f : G ⊗ (G ⊗ X) ⟶ X => f.left z)
    (ModObj.orbitComposition_snd G X)
  rw [show (snd G X).left ((ModObj.orbitComposition G X).left z) =
    (snd G X).left ((snd G (G ⊗ X)).left z) from he]

theorem saturation_mono {U V : Set X.left} (h : U ⊆ V) :
    saturation G X U ⊆ saturation G X V :=
  Set.image_mono (Set.preimage_mono h)

theorem saturation_eq_of_invariant (U : Set X.left)
    (hU : (γ[G, X]).left ⁻¹' U = (snd G X).left ⁻¹' U) :
    saturation G X U = U := by
  apply Set.Subset.antisymm _ (subset_saturation G X U)
  rintro x ⟨z, hz, rfl⟩
  exact (Set.ext_iff.mp hU z).mpr hz

@[simp] theorem saturation_idempotent (U : Set X.left) :
    saturation G X (saturation G X U) = saturation G X U :=
  saturation_eq_of_invariant G X _ (action_preimage_saturation G X U)

/-- Saturation is the least invariant subset containing the original set. -/
theorem saturation_subset_iff {U V : Set X.left}
    (hV : (γ[G, X]).left ⁻¹' V = (snd G X).left ⁻¹' V) :
    saturation G X U ⊆ V ↔ U ⊆ V := by
  constructor
  · exact (subset_saturation G X U).trans
  · intro h
    rw [← saturation_eq_of_invariant G X V hV]
    exact saturation_mono G X h

theorem saturation_isOpen (ha : IsOpenMap (γ[G, X]).left)
    {U : Set X.left} (hU : IsOpen U) : IsOpen (saturation G X U) :=
  ha _ (hU.preimage (snd G X).left.continuous)

end AlgebraicGeometry.GroupAction

#print axioms CategoryTheory.ModObj.orbitComposition_isPullback
#print axioms AlgebraicGeometry.GroupAction.action_preimage_saturation
#print axioms AlgebraicGeometry.GroupAction.saturation_subset_iff

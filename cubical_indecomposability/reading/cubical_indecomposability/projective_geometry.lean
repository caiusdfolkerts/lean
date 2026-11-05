import verification_bundle
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv

/-!
# Homogeneous projectivities and affine interface maps

A projectivity is represented by an invertible real linear map in one higher
dimension. Its action in the affine chart is division by the last coordinate.
Positivity is a property of that actual denominator on the specified set.

The normalized block used for Proposition 5 already has affine interfaces and
an affine cubical facet. The identity projectivity therefore witnesses the
paper's two projective assertions. These definitions retain their ordinary
mathematical meaning; invertibility is part of the type.
-/

set_option autoImplicit false

noncomputable section

namespace Papers.Polytopes

open Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

/-- An invertible homogeneous representative of a real projectivity. -/
abbrev HomogeneousProjectivity (d : ℕ) := E (d + 1) ≃ₗ[ℝ] E (d + 1)

/-- Embed the affine chart by appending the homogeneous coordinate one. -/
def homogeneousPoint {d : ℕ} (x : E d) : E (d + 1) :=
  WithLp.toLp 2 (Fin.lastCases 1 (fun i => x i))

/-- The denominator of a projectivity in the chosen affine chart. -/
def projectiveDenominator {d : ℕ} (T : HomogeneousProjectivity d) (x : E d) : ℝ :=
  T (homogeneousPoint x) (Fin.last d)

/-- The usual affine-chart action of an invertible homogeneous map. -/
def projectiveApply {d : ℕ} (T : HomogeneousProjectivity d) (x : E d) : E d :=
  WithLp.toLp 2 (fun i =>
    T (homogeneousPoint x) i.castSucc / projectiveDenominator T x)

def ProjectivelyPositiveOn {d : ℕ} (T : HomogeneousProjectivity d) (S : Set (E d)) : Prop :=
  ∀ x ∈ S, 0 < projectiveDenominator T x

@[simp] theorem projectiveDenominator_id {d : ℕ} (x : E d) :
    projectiveDenominator (LinearEquiv.refl ℝ (E (d + 1))) x = 1 := by
  simp [projectiveDenominator, homogeneousPoint]

@[simp] theorem projectiveApply_id {d : ℕ} (x : E d) :
    projectiveApply (LinearEquiv.refl ℝ (E (d + 1))) x = x := by
  ext i
  simp [projectiveApply, projectiveDenominator, homogeneousPoint]

theorem projectiveApply_id_fun {d : ℕ} :
    projectiveApply (LinearEquiv.refl ℝ (E (d + 1))) = (fun x : E d => x) :=
  funext projectiveApply_id

theorem projectivelyPositiveOn_id {d : ℕ} (S : Set (E d)) :
    ProjectivelyPositiveOn (LinearEquiv.refl ℝ (E (d + 1))) S := by
  intro x _
  simp

/-- Proposition 5(iv): one positive projectivity makes the interfaces
affinely equivalent, with their common face fixed pointwise. -/
def HasAffineInterfaceNormalization (P : ConvexPolytope 4)
    (F H Q : Set (E 4)) : Prop :=
  ∃ T : HomogeneousProjectivity 4, ProjectivelyPositiveOn T P.toSet ∧
    ∃ e : E 4 ≃ᵃ[ℝ] E 4,
      e '' (projectiveApply T '' F) = projectiveApply T '' H ∧
      ∀ x ∈ projectiveApply T '' Q, e x = x

/-- A nondegenerate parallelepiped is an injective affine image of a cube;
Proposition 5(v) permits an invertible projective change before that image. -/
def ProjectivelyParallelepiped (G : Set (E 4)) : Prop :=
  ∃ T : HomogeneousProjectivity 4, ProjectivelyPositiveOn T G ∧
    ∃ e : E 3 →ᵃ[ℝ] E 4, Function.Injective e ∧
      projectiveApply T '' G = e '' (standardCube 3).toSet

theorem affine_interface_normalization_of_affine
    (P : ConvexPolytope 4) (F H Q : Set (E 4))
    (e : E 4 ≃ᵃ[ℝ] E 4) (he : e '' F = H)
    (hfix : ∀ x ∈ Q, e x = x) :
    HasAffineInterfaceNormalization P F H Q := by
  refine ⟨LinearEquiv.refl ℝ (E 5), projectivelyPositiveOn_id _, e, ?_, ?_⟩
  · simpa only [projectiveApply_id_fun, Set.image_id'] using he
  · simpa only [projectiveApply_id_fun, Set.image_id'] using hfix

theorem projectivelyParallelepiped_of_affine (G : Set (E 4))
    (e : E 3 →ᵃ[ℝ] E 4) (hinj : Function.Injective e)
    (he : G = e '' (standardCube 3).toSet) : ProjectivelyParallelepiped G := by
  refine ⟨LinearEquiv.refl ℝ (E 5), projectivelyPositiveOn_id _, e, hinj, ?_⟩
  simpa only [projectiveApply_id_fun, Set.image_id'] using he

section AffineShear

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A rank-one affine shear, written without choosing coordinates. -/
def affineShearMap (l : V →ₗ[ℝ] ℝ) (v : V) (c : ℝ) : V →ᵃ[ℝ] V where
  toFun x := x + (l x + c) • v
  linear := LinearMap.id + l.smulRight v
  map_vadd' p x := by
    change (x + p) + (l (x + p) + c) • v =
      (x + l x • v) + (p + (l p + c) • v)
    rw [map_add]
    module

/-- If the shear direction lies in the kernel of its linear functional,
subtracting the same displacement is the inverse map. -/
def affineShear (l : V →ₗ[ℝ] ℝ) (v : V) (c : ℝ) (hv : l v = 0) : V ≃ᵃ[ℝ] V := by
  let inverse : V → V := fun x => x - (l x + c) • v
  have hleft : Function.LeftInverse inverse (affineShearMap l v c) := by
    intro x
    change x + (l x + c) • v - (l (x + (l x + c) • v) + c) • v = x
    simp [map_add, map_smul, hv]
  have hright : Function.RightInverse inverse (affineShearMap l v c) := by
    intro x
    change x - (l x + c) • v + (l (x - (l x + c) • v) + c) • v = x
    simp [map_sub, map_smul, hv]
  exact AffineEquiv.ofBijective ⟨hleft.injective, hright.surjective⟩

@[simp] theorem affineShear_apply (l : V →ₗ[ℝ] ℝ) (v : V) (c : ℝ)
    (hv : l v = 0) (x : V) : affineShear l v c hv x = x + (l x + c) • v := rfl

end AffineShear

end Papers.Polytopes

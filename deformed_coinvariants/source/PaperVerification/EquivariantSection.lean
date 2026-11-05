module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Module.LinearMap.End

/-!
# Averaging a homogeneous linear section

The maps in this file are actual linear maps. Averaging constructs a section
that intertwines the two finite group actions and retains every homogeneous
piece. No equivariant splitting is assumed as an extra hypothesis.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace PaperVerification.EquivariantSection

variable {K G V W : Type*} [Field K] [CharZero K] [Group G] [Fintype G]
variable [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

def average (ρ : G →* Module.End K V) (σ : G →* Module.End K W)
    (s : W →ₗ[K] V) : W →ₗ[K] V :=
  (Fintype.card G : K)⁻¹ • ∑ g : G, (ρ g⁻¹).comp (s.comp (σ g))

theorem average_apply (ρ : G →* Module.End K V) (σ : G →* Module.End K W)
    (s : W →ₗ[K] V) (x : W) :
    average ρ σ s x = (Fintype.card G : K)⁻¹ • ∑ g : G, ρ g⁻¹ (s (σ g x)) := by
  simp only [average, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply]

theorem average_rightInverse
    (ρ : G →* Module.End K V) (σ : G →* Module.End K W)
    (q : V →ₗ[K] W) (s : W →ₗ[K] V)
    (hq : ∀ g x, q (ρ g x) = σ g (q x)) (hs : ∀ x, q (s x) = x) (x : W) :
    q (average ρ σ s x) = x := by
  rw [average_apply, map_smul, map_sum]
  have hterm (g : G) : q (ρ g⁻¹ (s (σ g x))) = x := by
    rw [hq, hs, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply]
  simp only [hterm, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul K, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_smul]

theorem average_intertwines
    (ρ : G →* Module.End K V) (σ : G →* Module.End K W)
    (s : W →ₗ[K] V) (a : G) (x : W) :
    average ρ σ s (σ a x) = ρ a (average ρ σ s x) := by
  simp only [average_apply, map_smul, map_sum]
  congr 1
  refine Fintype.sum_bijective (fun g : G => g * a)
    (Group.mulRight_bijective a) _ _ ?_
  intro g
  have hright (y : V) : ρ a (ρ ((g * a)⁻¹) y) = ρ g⁻¹ y := by
    rw [← Module.End.mul_apply, ← map_mul]
    simp only [mul_inv_rev, mul_inv_cancel_left]
  rw [hright]
  congr 1
  rw [← Module.End.mul_apply, ← map_mul]

theorem average_preserves_pieces {D : Type*}
    (ρ : G →* Module.End K V) (σ : G →* Module.End K W)
    (s : W →ₗ[K] V) (A : D → Submodule K V) (B : D → Submodule K W)
    (hρ : ∀ g d x, x ∈ A d → ρ g x ∈ A d)
    (hσ : ∀ g d x, x ∈ B d → σ g x ∈ B d)
    (hs : ∀ d x, x ∈ B d → s x ∈ A d) :
    ∀ d x, x ∈ B d → average ρ σ s x ∈ A d := by
  intro d x hx
  rw [average_apply]
  apply (A d).smul_mem
  apply (A d).sum_mem
  intro g _
  exact hρ g⁻¹ d _ (hs d _ (hσ g d x hx))

/-- Averaging any given homogeneous section supplies an equivariant one.
The required underlying section is constructed from homogeneous Milnor lifts
in the hypersurface application. -/
theorem exists_homogeneous_equivariant_section {D : Type*}
    (ρ : G →* Module.End K V) (σ : G →* Module.End K W)
    (q : V →ₗ[K] W) (s : W →ₗ[K] V)
    (A : D → Submodule K V) (B : D → Submodule K W)
    (hq : ∀ g x, q (ρ g x) = σ g (q x)) (hsq : ∀ x, q (s x) = x)
    (hρ : ∀ g d x, x ∈ A d → ρ g x ∈ A d)
    (hσ : ∀ g d x, x ∈ B d → σ g x ∈ B d)
    (hs : ∀ d x, x ∈ B d → s x ∈ A d) :
    ∃ s' : W →ₗ[K] V,
      (∀ x, q (s' x) = x) ∧
      (∀ g x, s' (σ g x) = ρ g (s' x)) ∧
      ∀ d x, x ∈ B d → s' x ∈ A d :=
  ⟨average ρ σ s, average_rightInverse ρ σ q s hq hsq,
    average_intertwines ρ σ s, average_preserves_pieces ρ σ s A B hρ hσ hs⟩

end PaperVerification.EquivariantSection

module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Actual exposed faces of Minkowski sums

The face is the set of maximizers of a linear functional on the actual
set of points.  These statements have no face-lattice or summand
certificates among their hypotheses.  In finite-dimensional Euclidean
space they agree with Mathlib's continuous exposed-face definition.
-/

namespace Papers.MinkowskiFaces

open Set
open scoped Pointwise

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

def maxFace (S : Set E) (u : E →ₗ[ℝ] ℝ) : Set E :=
  {x ∈ S | ∀ y ∈ S, u y ≤ u x}

theorem maxFace_subset (S : Set E) (u : E →ₗ[ℝ] ℝ) :
    maxFace S u ⊆ S := fun _ h => h.1

theorem components_maximize {S T : Set E} {u : E →ₗ[ℝ] ℝ}
    {a b : E} (ha : a ∈ S) (hb : b ∈ T)
    (hab : a + b ∈ maxFace (S + T) u) :
    a ∈ maxFace S u ∧ b ∈ maxFace T u := by
  constructor
  · refine ⟨ha, ?_⟩
    intro x hx
    have h := hab.2 (x + b) (Set.mem_add.mpr ⟨x, hx, b, hb, rfl⟩)
    simpa only [map_add, add_le_add_iff_right] using h
  · refine ⟨hb, ?_⟩
    intro y hy
    have h := hab.2 (a + y) (Set.mem_add.mpr ⟨a, ha, y, hy, rfl⟩)
    simpa only [map_add, add_le_add_iff_left] using h

theorem maxFace_add (S T : Set E) (u : E →ₗ[ℝ] ℝ) :
    maxFace (S + T) u = maxFace S u + maxFace T u := by
  ext z
  constructor
  · intro hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp hz.1
    obtain ⟨hfa, hfb⟩ := components_maximize ha hb hz
    exact Set.mem_add.mpr ⟨a, hfa, b, hfb, rfl⟩
  · intro hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp hz
    refine ⟨Set.mem_add.mpr ⟨a, ha.1, b, hb.1, rfl⟩, ?_⟩
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_add.mp hz
    simpa only [map_add] using add_le_add (ha.2 x hx) (hb.2 y hy)

theorem maxFace_eq_of_constant (S : Set E) (u : E →ₗ[ℝ] ℝ)
    (h : ∀ x ∈ S, ∀ y ∈ S, u x = u y) :
    maxFace S u = S := by
  apply Set.Subset.antisymm (maxFace_subset S u)
  intro x hx
  exact ⟨hx, fun y hy => le_of_eq (h y hy x hx)⟩

theorem maxFace_add_of_constant_left (S T : Set E) (u : E →ₗ[ℝ] ℝ)
    (h : ∀ x ∈ S, ∀ y ∈ S, u (x - y) = 0) :
    maxFace (S + T) u = S + maxFace T u := by
  rw [maxFace_add, maxFace_eq_of_constant S u]
  intro x hx y hy
  exact sub_eq_zero.mp (by simpa only [map_sub] using h x hx y hy)

theorem maxFace_linear_image (S : Set E) (L : E →ₗ[ℝ] F)
    (u : F →ₗ[ℝ] ℝ) :
    maxFace (L '' S) u = L '' maxFace S (u.comp L) := by
  ext z
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hmax⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    intro y hy
    exact hmax (L y) ⟨y, hy, rfl⟩
  · rintro ⟨x, ⟨hx, hmax⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro z ⟨y, hy, rfl⟩
    exact hmax y hy

theorem maxFace_translate (S : Set E) (u : E →ₗ[ℝ] ℝ) (b : E) :
    maxFace ((fun x => x + b) '' S) u =
      (fun x => x + b) '' maxFace S u := by
  ext z
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hmax⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    intro y hy
    have h := hmax (y + b) ⟨y, hy, rfl⟩
    simpa only [map_add, add_le_add_iff_right] using h
  · rintro ⟨x, ⟨hx, hmax⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro z ⟨y, hy, rfl⟩
    simpa only [map_add, add_le_add_iff_right] using hmax y hy

theorem maxFace_positive_smul (S : Set E) (u : E →ₗ[ℝ] ℝ)
    {a : ℝ} (ha : 0 < a) :
    maxFace ((fun x => a • x) '' S) u =
      (fun x => a • x) '' maxFace S u := by
  ext z
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hmax⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    intro y hy
    have h := hmax (a • y) ⟨y, hy, rfl⟩
    exact (mul_le_mul_iff_of_pos_left ha).mp (by simpa only [map_smul, smul_eq_mul] using h)
  · rintro ⟨x, ⟨hx, hmax⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro z ⟨y, hy, rfl⟩
    simpa only [map_smul, smul_eq_mul] using
      (mul_le_mul_iff_of_pos_left ha).mpr (hmax y hy)

section Continuous
variable [TopologicalSpace E]

theorem maxFace_eq_toExposed (S : Set E) (u : E →L[ℝ] ℝ) :
    maxFace S u.toLinearMap = u.toExposed S := rfl

end Continuous
end Papers.MinkowskiFaces

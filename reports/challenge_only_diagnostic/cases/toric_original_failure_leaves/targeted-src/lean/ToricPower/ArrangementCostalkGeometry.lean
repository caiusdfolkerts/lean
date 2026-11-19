module

public import ToricPower.PolyhedralFoundations
public import Mathlib.Analysis.Convex.GaugeRescale

/-!
# The literal convex regions in the cellular costalk calculation

An arrangement open star is already convex. Intersecting it with the open
monomial inequalities therefore gives an actual open convex polyhedron.
A strict direction on the selected forms proves the exact nonemptiness
criterion, including points on the boundary. Coordinate augmentation makes
the region bounded, and a genuine ambient homeomorphism takes it, its
closure, and its frontier to the open ball, closed ball, and sphere.

These are geometric inputs to a relative cellular cochain computation.
This file does not assume or assert the missing cochain comparison.
-/

@[expose] public noncomputable section

open Set Metric Topology
open scoped Classical

namespace ToricPower.IntegralArrangement

section Linear

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E]

/-- The monomial support of the reflected dual Cartier label. -/
def openWeightRegion (f : ι → E →ₗ[ℝ] ℝ) (selected : Set ι) (weight : ι → ℤ) : Set E :=
  {y | ∀ i ∈ selected, f i y < (weight i : ℝ) + 1}

/-- The actual open region occurring at an arrangement representable. -/
def costalkRegion (f : ι → E →ₗ[ℝ] ℝ) (selected : Set ι) (weight : ι → ℤ)
    (x : E) : Set E :=
  localStar f x ∩ openWeightRegion f selected weight

theorem openWeightRegion_convex (f : ι → E →ₗ[ℝ] ℝ)
    (selected : Set ι) (weight : ι → ℤ) : Convex ℝ (openWeightRegion f selected weight) := by
  simp only [openWeightRegion, Set.setOf_forall]
  exact convex_iInter fun i => convex_iInter fun _ =>
    (convex_Iio ((weight i : ℝ) + 1)).linear_preimage (f i)

theorem costalkRegion_convex (f : ι → E →ₗ[ℝ] ℝ)
    (selected : Set ι) (weight : ι → ℤ) (x : E) :
    Convex ℝ (costalkRegion f selected weight x) :=
  (localStar_convex f x).inter (openWeightRegion_convex f selected weight)

/-- Any point of the costalk region forces the weak inequalities at the
original cell. Integer spacing of the arrangement is used here. -/
theorem costalkRegion_nonempty_imp (f : ι → E →ₗ[ℝ] ℝ)
    (selected : Set ι) (weight : ι → ℤ) (x : E)
    (nonempty : (costalkRegion f selected weight x).Nonempty) :
    ∀ i ∈ selected, f i x ≤ (weight i : ℝ) + 1 := by
  obtain ⟨y, inStar, inWeight⟩ := nonempty
  intro i hi
  have lower := (inStar i).1
  have upper := inWeight i hi
  have ceiling_lt : (⌈f i x⌉ : ℝ) < (weight i : ℝ) + 2 := by linarith
  have integer_lt : ⌈f i x⌉ < weight i + 2 := by exact_mod_cast ceiling_lt
  have integer_le : ⌈f i x⌉ ≤ weight i + 1 := by omega
  exact (Int.le_ceil _).trans (by exact_mod_cast integer_le)

end Linear

section Topology

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Finite ι]

/-- Open inequalities on finitely many continuous linear forms. -/
theorem openWeightRegion_isOpen (f : ι → E →ₗ[ℝ] ℝ)
    (selected : Set ι) (weight : ι → ℤ) : IsOpen (openWeightRegion f selected weight) := by
  simp only [openWeightRegion, Set.setOf_forall]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro _
  exact isOpen_lt (f i).continuous_of_finiteDimensional continuous_const

theorem costalkRegion_isOpen (f : ι → E →ₗ[ℝ] ℝ)
    (selected : Set ι) (weight : ι → ℤ) (x : E) :
    IsOpen (costalkRegion f selected weight x) :=
  (localStar_isOpen f (fun i => (f i).continuous_of_finiteDimensional) x).inter
    (openWeightRegion_isOpen f selected weight)

/-- A common strictly positive direction supplies points of the region
arbitrarily near the cell, even when its center lies on a boundary wall. -/
theorem costalkRegion_nonempty_iff (f : ι → E →ₗ[ℝ] ℝ)
    (selected : Set ι) (weight : ι → ℤ) (x : E)
    (strictDirection : ∃ v : E, ∀ i ∈ selected, 0 < f i v) :
    (costalkRegion f selected weight x).Nonempty ↔
      ∀ i ∈ selected, f i x ≤ (weight i : ℝ) + 1 := by
  refine ⟨costalkRegion_nonempty_imp f selected weight x, ?_⟩
  intro bounds
  obtain ⟨v, positive⟩ := strictDirection
  let neighborhood : Set E := (fun z => x + z) ⁻¹' localStar f x
  have openNeighborhood : IsOpen neighborhood :=
    (localStar_isOpen f (fun i => (f i).continuous_of_finiteDimensional) x).preimage
      (continuous_const.add continuous_id)
  have zero_mem : (0 : E) ∈ neighborhood := by
    simpa only [neighborhood, Set.mem_preimage, add_zero] using mem_localStar_self f x
  obtain ⟨t, ht, near⟩ := LocalMorse.exists_negative_smul_mem openNeighborhood zero_mem v
  refine ⟨x + (-t) • v, near, ?_⟩
  intro i hi
  change f i (x + (-t) • v) < (weight i : ℝ) + 1
  rw [map_add, map_smul, smul_eq_mul]
  have hp := mul_pos ht (positive i hi)
  nlinarith [bounds i hi]

/-- The weak real inequalities are exactly the integer section
inequalities for the canonical-bundle-corrected Cartier label. -/
theorem costalkRegion_nonempty_iff_integer (f : ι → E →ₗ[ℝ] ℝ)
    (selected : Set ι) (weight : ι → ℤ) (x : E)
    (strictDirection : ∃ v : E, ∀ i ∈ selected, 0 < f i v) :
    (costalkRegion f selected weight x).Nonempty ↔
      ∀ i ∈ selected, ⌈f i x⌉ - 1 ≤ weight i := by
  rw [costalkRegion_nonempty_iff f selected weight x strictDirection]
  simp only [sub_le_iff_le_add, Int.ceil_le, Int.cast_add, Int.cast_one]

end Topology

section Coordinates

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)

/-- Coordinate hyperplanes give a concrete compact box containing the
whole open star; no spanning hypothesis on the original rows is needed. -/
theorem augmented_localStar_bounded (x : Fin n → ℝ) :
    Bornology.IsBounded (localStar (augmentedForms A) x) := by
  apply (isCompact_Icc (a := fun j : Fin n => (⌈x j⌉ : ℝ) - 1)
    (b := fun j : Fin n => (⌈x j⌉ : ℝ) + 1)).isBounded.subset
  intro y hy
  constructor <;> intro j
  · have h := (hy (Sum.inr j)).1
    simpa only [augmentedForms, Sum.elim_inr, LinearMap.proj_apply] using h.le
  · have h := (hy (Sum.inr j)).2
    change y j < (⌈x j⌉ : ℝ) + (if x j = (⌈x j⌉ : ℝ) then 1 else 0) at h
    have hone : (if x j = (⌈x j⌉ : ℝ) then (1 : ℝ) else 0) ≤ 1 := by
      split_ifs <;> norm_num
    change y j ≤ (⌈x j⌉ : ℝ) + 1
    linarith

/-- A literal ambient homeomorphism identifies the nonempty costalk
region, its closure, and its frontier with the three standard ball sets. -/
theorem augmentedCostalkRegion_ball_chart
    (selected : Set (Fin s ⊕ Fin n)) (weight : Fin s ⊕ Fin n → ℤ)
    (x : Fin n → ℝ)
    (nonempty : (costalkRegion (augmentedForms A) selected weight x).Nonempty) :
    ∃ chart : (Fin n → ℝ) ≃ₜ (Fin n → ℝ),
      chart '' costalkRegion (augmentedForms A) selected weight x = ball 0 1 ∧
      chart '' closure (costalkRegion (augmentedForms A) selected weight x) = closedBall 0 1 ∧
      chart '' frontier (costalkRegion (augmentedForms A) selected weight x) = sphere 0 1 := by
  have openRegion := costalkRegion_isOpen (augmentedForms A) selected weight x
  have convexRegion := costalkRegion_convex (augmentedForms A) selected weight x
  have bounded := (augmented_localStar_bounded A x).subset
    (show costalkRegion (augmentedForms A) selected weight x ⊆
      localStar (augmentedForms A) x from Set.inter_subset_left)
  simpa only [openRegion.interior_eq] using
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall convexRegion
      (by simpa only [openRegion.interior_eq] using nonempty) bounded

end Coordinates
end ToricPower.IntegralArrangement

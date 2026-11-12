module

public import Mathlib.Analysis.Convex.Contractible

/-!
# The elementary contraction behind the local sheaf test

At a boundary point of an open polyhedral cone, a covector outside the
negative normal cone admits a vector pointing strictly into the polyhedron
and into the positive halfspace.  Its negative, scaled into a sufficiently
small convex neighborhood, is a common center for the union of the violated
closed halfspaces.  This file proves the resulting star-shaped contraction
for the literal sets; there is no assumed acyclicity statement.
-/

@[expose] public noncomputable section

namespace ToricPower.LocalMorse

open Set

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E]

/-- The negative half of a chosen convex neighborhood. -/
def negativeHalf (B : Set E) (ξ : E →ₗ[ℝ] ℝ) : Set E :=
  B ∩ ξ ⁻¹' Iio 0

/-- The complement of the strict polyhedral inequalities in the negative
half-neighborhood.  The index type lists the active boundary inequalities. -/
def excludedRegion (B : Set E) (ξ : E →ₗ[ℝ] ℝ)
    (f : ι → E →ₗ[ℝ] ℝ) : Set E :=
  negativeHalf B ξ ∩ ⋃ i, (f i) ⁻¹' Iic 0

theorem negativeHalf_convex {B : Set E} (hB : Convex ℝ B)
    (ξ : E →ₗ[ℝ] ℝ) : Convex ℝ (negativeHalf B ξ) :=
  hB.inter ((convex_Iio (0 : ℝ)).linear_preimage ξ)

/-- A point satisfying every opposite weak inequality is a star center
of the entire excluded region, although this union need not be convex. -/
theorem excludedRegion_starConvex {B : Set E} (hB : Convex ℝ B)
    (ξ : E →ₗ[ℝ] ℝ) (f : ι → E →ₗ[ℝ] ℝ) {p : E}
    (hpB : p ∈ B) (hpξ : ξ p < 0) (hpf : ∀ i, f i p ≤ 0) :
    StarConvex ℝ p (excludedRegion B ξ f) := by
  exact ((negativeHalf_convex hB ξ).starConvex ⟨hpB, hpξ⟩).inter
    (starConvex_iUnion fun i =>
      ((convex_Iic (0 : ℝ)).linear_preimage (f i)).starConvex (hpf i))

theorem mem_excludedRegion_center [Nonempty ι]
    (B : Set E) (ξ : E →ₗ[ℝ] ℝ) (f : ι → E →ₗ[ℝ] ℝ) {p : E}
    (hpB : p ∈ B) (hpξ : ξ p < 0) (hpf : ∀ i, f i p ≤ 0) :
    p ∈ excludedRegion B ξ f := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact ⟨⟨hpB, hpξ⟩, mem_iUnion.mpr ⟨i, hpf i⟩⟩

section Topology

variable [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]

/-- The actual radial homotopy from a chosen star center to the identity. -/
def radialHomotopy {S : Set E} {p : E} (hS : StarConvex ℝ p S) (hp : p ∈ S) :
    ContinuousMap.Homotopy (ContinuousMap.const S (⟨p, hp⟩ : S))
      (ContinuousMap.id S) where
  toFun q := ⟨(1 - (q.1 : ℝ)) • p + (q.1 : ℝ) • (q.2 : E),
    hS q.2.property (sub_nonneg.mpr q.1.property.2) q.1.property.1
      (sub_add_cancel 1 (q.1 : ℝ))⟩
  continuous_toFun := by fun_prop
  map_zero_left q := by simp
  map_one_left q := by simp

/-- The literal inclusion of the excluded set into the half-neighborhood
is a homotopy equivalence.  Its inverse is the constant map at the common
star center; both inverse homotopies are explicitly radial. -/
def excludedRegionInclusionHomotopyEquiv [Nonempty ι]
    {B : Set E} (hB : Convex ℝ B) (ξ : E →ₗ[ℝ] ℝ)
    (f : ι → E →ₗ[ℝ] ℝ) {p : E}
    (hpB : p ∈ B) (hpξ : ξ p < 0) (hpf : ∀ i, f i p ≤ 0) :
    ContinuousMap.HomotopyEquiv (excludedRegion B ξ f) (negativeHalf B ξ) where
  toFun := ⟨fun x => ⟨x.val, x.property.1⟩, by fun_prop⟩
  invFun := ContinuousMap.const _ ⟨p, mem_excludedRegion_center B ξ f hpB hpξ hpf⟩
  left_inv := ⟨radialHomotopy (excludedRegion_starConvex hB ξ f hpB hpξ hpf)
    (mem_excludedRegion_center B ξ f hpB hpξ hpf)⟩
  right_inv := ⟨radialHomotopy ((negativeHalf_convex hB ξ).starConvex ⟨hpB, hpξ⟩)
    ⟨hpB, hpξ⟩⟩

/-- The negative half-neighborhood is genuinely contractible. -/
def negativeHalf_contractible {B : Set E} (hB : Convex ℝ B)
    (ξ : E →ₗ[ℝ] ℝ) {p : E} (hpB : p ∈ B) (hpξ : ξ p < 0) :
    ContractibleSpace (negativeHalf B ξ) :=
  (negativeHalf_convex hB ξ).contractibleSpace ⟨p, hpB, hpξ⟩

/-- The excluded set is genuinely contractible at a boundary stratum.
In the no-active-inequality case the sheaf is locally constant instead. -/
def excludedRegion_contractible [Nonempty ι]
    {B : Set E} (hB : Convex ℝ B) (ξ : E →ₗ[ℝ] ℝ)
    (f : ι → E →ₗ[ℝ] ℝ) {p : E}
    (hpB : p ∈ B) (hpξ : ξ p < 0) (hpf : ∀ i, f i p ≤ 0) :
    ContractibleSpace (excludedRegion B ξ f) :=
  (excludedRegion_starConvex hB ξ f hpB hpξ hpf).contractibleSpace
    ⟨p, mem_excludedRegion_center B ξ f hpB hpξ hpf⟩

end Topology

end ToricPower.LocalMorse

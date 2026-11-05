module

public import volume_polynomials.mixed_volume_basis_part01
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section
set_option autoImplicit false

/-!
# Coordinate projection volumes of actual convex bodies

These definitions use Mathlib's nonempty compact convex sets and Lebesgue
measure on the retained coordinate space. Lower-dimensional bodies are allowed.
The topology on arrays is the ordinary finite product topology.
-/

noncomputable section
open Set MeasureTheory
open scoped Pointwise

namespace RankThreeProjection

abbrev Space (n : ℕ) := Fin n → ℝ
abbrev Body (n : ℕ) := ConvexBody (Space n)
abbrev Array (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- Coordinates retained after deleting the finite set `I`. -/
abbrev Retained {n : ℕ} (I : Finset (Fin n)) := {j : Fin n // j ∉ I}

/-- The literal coordinate restriction map. -/
def deleteCoordinates {n : ℕ} (I : Finset (Fin n)) :
    Space n →L[ℝ] (Retained I → ℝ) :=
  ContinuousLinearMap.pi (fun j => ContinuousLinearMap.proj j.val)

/-- A projection body is the image under coordinate deletion. -/
def projectedBody {n : ℕ} (I : Finset (Fin n)) (K : Body n) :
    ConvexBody (Retained I → ℝ) :=
  VolumePolynomials.mapBody (deleteCoordinates I) K

/-- Ordinary Lebesgue volume in the retained coordinate space. -/
def coordinateVolume {n : ℕ} (I : Finset (Fin n)) (K : Body n) : ℝ :=
  volume.real (projectedBody I K : Set (Retained I → ℝ))

/-- The hollow complementary projection-volume array from the paper. -/
def projectionArray {n : ℕ} (K : Body n) : Array n := fun i j =>
  if i = j then 0 else coordinateVolume {i, j} K

/-- The actual realization locus; no geometric properties are built into it. -/
def projectionLocus (n : ℕ) : Set (Array n) := Set.range (projectionArray (n := n))

/-- The closure in the finite-dimensional space of all arrays. -/
def closedProjectionLocus (n : ℕ) : Set (Array n) := closure (projectionLocus n)

/-- The three elementary hypotheses appearing in the principal theorem. -/
def PositiveHollowSymmetric {n : ℕ} (P : Array n) : Prop :=
  (∀ i, P i i = 0) ∧ (∀ i j, P i j = P j i) ∧ (∀ i j, i ≠ j → 0 < P i j)

@[simp] theorem deleteCoordinates_apply {n : ℕ} (I : Finset (Fin n))
    (x : Space n) (j : Retained I) : deleteCoordinates I x j = x j.val := rfl

@[simp] theorem projectedBody_coe {n : ℕ} (I : Finset (Fin n)) (K : Body n) :
    (projectedBody I K : Set (Retained I → ℝ)) = deleteCoordinates I '' (K : Set (Space n)) := rfl

@[simp] theorem projectionArray_diagonal {n : ℕ} (K : Body n) (i : Fin n) :
    projectionArray K i i = 0 := by simp [projectionArray]

theorem projectionArray_symmetric {n : ℕ} (K : Body n) (i j : Fin n) :
    projectionArray K i j = projectionArray K j i := by
  by_cases h : i = j
  · subst j; rfl
  · simp only [projectionArray, if_neg h, if_neg (Ne.symm h)]
    congr 1
    exact Finset.pair_comm i j

theorem projectionArray_nonnegative {n : ℕ} (K : Body n) (i j : Fin n) :
    0 ≤ projectionArray K i j := by
  unfold projectionArray
  split_ifs
  · exact le_rfl
  · exact ENNReal.toReal_nonneg

theorem projectionArray_mem_closed {n : ℕ} (K : Body n) :
    projectionArray K ∈ closedProjectionLocus n :=
  subset_closure ⟨K, rfl⟩

theorem isClosed_closedProjectionLocus (n : ℕ) : IsClosed (closedProjectionLocus n) :=
  isClosed_closure

end RankThreeProjection

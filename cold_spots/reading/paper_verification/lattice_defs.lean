module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.Group.Int.Even
public import Mathlib.Algebra.BigOperators.Fin
@[expose] public section
/-!
# Coordinate definitions for the lattices in the cold-spots manuscript

`sqDist` is the sum of the coordinate squares, hence the squared Euclidean
distance, not the squared norm on the unbundled function space.
`dPlusSet` is exactly D_n ∪ (D_n + (1/2,...,1/2)).
-/

noncomputable section

open scoped BigOperators

namespace PaperVerification.ColdSpots

def intVec {n : ℕ} (z : Fin n → ℤ) : Fin n → ℝ := fun i ↦ (z i : ℝ)

def sqDist {n : ℕ} (x y : Fin n → ℝ) : ℝ := ∑ i, (x i - y i) ^ 2

def dSet (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ∃ z : Fin n → ℤ, Even (∑ i, z i) ∧ x = intVec z}

def dPlusSet (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ∃ z : Fin n → ℤ, Even (∑ i, z i) ∧
    (x = intVec z ∨ x = fun i ↦ (z i : ℝ) + 1 / 2)}

def squaredDepth {n : ℕ} (L : Set (Fin n → ℝ)) (x : Fin n → ℝ) : ℝ :=
  sInf ((fun z ↦ sqDist x z) '' L)

def IsDeepHole {n : ℕ} (L : Set (Fin n → ℝ)) (x : Fin n → ℝ) : Prop :=
  ∀ y, squaredDepth L y ≤ squaredDepth L x

lemma sqDist_nonneg {n : ℕ} (x y : Fin n → ℝ) : 0 ≤ sqDist x y :=
  Finset.sum_nonneg fun i _ ↦ sq_nonneg _

lemma sqDist_comm {n : ℕ} (x y : Fin n → ℝ) : sqDist x y = sqDist y x := by
  apply Finset.sum_congr rfl
  intro i _
  exact sub_sq_comm (x i) (y i)

/-- The coordinate expression is exactly the squared Euclidean norm. -/
theorem sqDist_eq_euclidean_norm_sq {n : ℕ} (x y : Fin n → ℝ) :
    sqDist x y =
      ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) - WithLp.toLp 2 y‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

lemma zero_mem_dPlusSet (n : ℕ) : 0 ∈ dPlusSet n := by
  refine ⟨0, by simp, Or.inl ?_⟩
  ext i
  simp [intVec]

lemma dPlusSet_nonempty (n : ℕ) : (dPlusSet n).Nonempty :=
  ⟨0, zero_mem_dPlusSet n⟩

lemma squaredDepth_nonneg {n : ℕ} (L : Set (Fin n → ℝ)) (hL : L.Nonempty)
    (x : Fin n → ℝ) : 0 ≤ squaredDepth L x := by
  exact le_csInf (hL.image _) (by rintro r ⟨z, hz, rfl⟩; exact sqDist_nonneg _ _)

lemma squaredDepth_le {n : ℕ} {L : Set (Fin n → ℝ)} (x : Fin n → ℝ)
    {z : Fin n → ℝ} (hz : z ∈ L) : squaredDepth L x ≤ sqDist x z := by
  exact csInf_le ⟨0, by rintro r ⟨w, hw, rfl⟩; exact sqDist_nonneg _ _⟩ ⟨z, hz, rfl⟩

end PaperVerification.ColdSpots

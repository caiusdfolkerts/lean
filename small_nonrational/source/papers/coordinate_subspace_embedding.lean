module
public import Papers.RelativeTwoGroupsDensity

@[expose] public section
noncomputable section

open Matrix Module Set Filter Topology
open scoped BigOperators

namespace Papers.RationalityTen.FixedCoordinateFlagDensity

open ChirotopeDensity PlaneRationalization

/-- The coordinate inclusion associated with an injection of finite labels. -/
def coordinateInclusion {p s : ℕ} (e : Fin p → Fin s) : Matrix (Fin s) (Fin p) ℝ :=
  fun i j => if e j = i then 1 else 0

theorem coordinateInclusion_mul_at {p s n : ℕ} (e : Fin p → Fin s)
    (he : Function.Injective e) (D : Matrix (Fin p) (Fin n) ℝ) (a : Fin p) (j : Fin n) :
    (coordinateInclusion e * D) (e a) j = D a j := by
  classical
  simp only [Matrix.mul_apply, coordinateInclusion]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hba
    have hne : e b ≠ e a := fun h => hba (he h)
    simp only [hne, if_false, zero_mul]
  · exact fun h => (h (Finset.mem_univ a)).elim

theorem coordinateInclusion_mul_outside {p s n : ℕ} (e : Fin p → Fin s)
    (D : Matrix (Fin p) (Fin n) ℝ) (i : Fin s) (hi : i ∉ Set.range e) (j : Fin n) :
    (coordinateInclusion e * D) i j = 0 := by
  classical
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro a _
  have hne : e a ≠ i := fun h => hi ⟨a, h⟩
  simp only [coordinateInclusion, hne, if_false, zero_mul]

theorem coordinateInclusion_transpose_mul {p s n : ℕ} (e : Fin p → Fin s)
    (C : Matrix (Fin s) (Fin n) ℝ) (a : Fin p) (j : Fin n) :
    ((coordinateInclusion e).transpose * C) a j = C (e a) j := by
  classical
  simp only [Matrix.transpose_apply, Matrix.mul_apply, coordinateInclusion]
  rw [Finset.sum_eq_single (e a)]
  · simp
  · intro i _ hie
    simp only [Ne.symm hie, if_false, zero_mul]
  · exact fun h => (h (Finset.mem_univ (e a))).elim

theorem coordinateInclusion_restrict_mul {p s n : ℕ} (e : Fin p → Fin s)
    (he : Function.Injective e) (D : Matrix (Fin p) (Fin n) ℝ) :
    (coordinateInclusion e).transpose * (coordinateInclusion e * D) = D := by
  ext a j
  rw [coordinateInclusion_transpose_mul, coordinateInclusion_mul_at e he]

theorem coordinateInclusion_reconstruct {p s n : ℕ} (e : Fin p → Fin s)
    (he : Function.Injective e) (C : Matrix (Fin s) (Fin n) ℝ)
    (hC : ∀ i, i ∉ Set.range e → ∀ j, C i j = 0) :
    coordinateInclusion e * ((coordinateInclusion e).transpose * C) = C := by
  ext i j
  by_cases hi : i ∈ Set.range e
  · obtain ⟨a, rfl⟩ := hi
    rw [coordinateInclusion_mul_at e he, coordinateInclusion_transpose_mul]
  · rw [coordinateInclusion_mul_outside e _ i hi j, hC i hi j]

theorem coordinateInclusion_mul_rank {p s n : ℕ} (e : Fin p → Fin s)
    (he : Function.Injective e) (D : Matrix (Fin p) (Fin n) ℝ) :
    (coordinateInclusion e * D).rank = D.rank := by
  apply Nat.le_antisymm (Matrix.rank_mul_le_right _ _)
  have h := Matrix.rank_mul_le_right (coordinateInclusion e).transpose
    (coordinateInclusion e * D)
  rw [coordinateInclusion_restrict_mul e he D] at h
  exact h

theorem coordinateInclusion_rational {p s : ℕ} (e : Fin p → Fin s) :
    RationalCoordinates (coordinateInclusion e) := by
  intro i j
  by_cases h : e j = i
  · exact ⟨1, by simp [coordinateInclusion, h]⟩
  · exact ⟨0, by simp [coordinateInclusion, h]⟩

theorem mul_coordinateInclusion {p s m : ℕ} (e : Fin p → Fin s)
    (A : Matrix (Fin m) (Fin s) ℝ) (i : Fin m) (a : Fin p) :
    (A * coordinateInclusion e) i a = A i (e a) := by
  classical
  simp only [Matrix.mul_apply, coordinateInclusion]
  rw [Finset.sum_eq_single (e a)]
  · simp
  · intro j _ hje
    simp only [Ne.symm hje, if_false, mul_zero]
  · exact fun h => (h (Finset.mem_univ (e a))).elim

theorem subsetRank_comp_image {p s m : ℕ}
    (q : Fin s → Fin m → ℝ) (e : Fin p → Fin s) (S : Finset (Fin p)) :
    subsetRank (fun i => q (e i)) S = subsetRank q (S.image e) := by
  have hs : (fun i => q (e i)) '' (↑S : Set (Fin p)) =
      q '' (↑(S.image e) : Set (Fin s)) := by
    ext v
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨e i, Finset.mem_image.mpr ⟨i, hi, rfl⟩, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      exact ⟨i, hi, rfl⟩
  unfold subsetRank
  rw [hs]

theorem sameSubsetRanks_mul_coordinateInclusion {p s m : ℕ}
    (e : Fin p → Fin s) (A B : Matrix (Fin m) (Fin s) ℝ)
    (h : SameSubsetRanks A.col B.col) :
    SameSubsetRanks (A * coordinateInclusion e).col (B * coordinateInclusion e).col := by
  have hA : (A * coordinateInclusion e).col = fun i => A.col (e i) := by
    ext a j
    exact mul_coordinateInclusion e A j a
  have hB : (B * coordinateInclusion e).col = fun i => B.col (e i) := by
    ext a j
    exact mul_coordinateInclusion e B j a
  intro S
  rw [hA, hB]
  exact (subsetRank_comp_image A.col e S).trans
    ((h (S.image e)).trans (subsetRank_comp_image B.col e S).symm)

#print axioms coordinateInclusion_reconstruct
#print axioms sameSubsetRanks_mul_coordinateInclusion

end Papers.RationalityTen.FixedCoordinateFlagDensity

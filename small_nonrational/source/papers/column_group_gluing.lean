module
public import Papers.CoordinateSubspaceEmbedding

@[expose] public section
noncomputable section

open Matrix Module Set Filter Topology
open scoped BigOperators

namespace Papers.RationalityTen.FixedCoordinateFlagDensity

open ChirotopeDensity PlaneRationalization

/-- Retain a specified group of columns and zero the others. -/
def columnMask {p n : ℕ} (C : Matrix (Fin p) (Fin n) ℝ)
    (J : Finset (Fin n)) : Matrix (Fin p) (Fin n) ℝ :=
  fun i j => if j ∈ J then C i j else 0

theorem columnMask_col_mem {p n : ℕ} (C : Matrix (Fin p) (Fin n) ℝ)
    (J : Finset (Fin n)) {j : Fin n} (hj : j ∈ J) :
    (columnMask C J).col j = C.col j := by
  ext i
  simp only [columnMask, Matrix.col_apply, if_pos hj]

theorem columnMask_rank {p n : ℕ} (C : Matrix (Fin p) (Fin n) ℝ)
    (J : Finset (Fin n)) : (columnMask C J).rank = subsetRank C.col J := by
  have hs : Submodule.span ℝ (Set.range (columnMask C J).col) =
      Submodule.span ℝ (C.col '' (↑J : Set (Fin n))) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      by_cases hj : j ∈ J
      · rw [columnMask_col_mem C J hj]
        exact Submodule.subset_span ⟨j, hj, rfl⟩
      · have hz : (columnMask C J).col j = 0 := by
          ext i
          simp [columnMask, Matrix.col_apply, hj]
        rw [hz]
        exact Submodule.zero_mem _
    · apply Submodule.span_le.mpr
      rintro _ ⟨j, hj, rfl⟩
      rw [← columnMask_col_mem C J hj]
      exact Submodule.subset_span (Set.mem_range_self j)
  rw [Matrix.rank_eq_finrank_span_cols]
  unfold subsetRank
  rw [hs]

theorem columnMask_mul_zero {m p n : ℕ} (A : Matrix (Fin m) (Fin p) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ) (J : Finset (Fin n)) (h : A * C = 0) :
    A * columnMask C J = 0 := by
  ext i j
  by_cases hj : j ∈ J
  · simpa [Matrix.mul_apply, columnMask, hj] using congrFun (congrFun h i) j
  · simp [Matrix.mul_apply, columnMask, hj]

theorem columnMask_continuous {p n : ℕ} (J : Finset (Fin n)) :
    Continuous (fun C : Matrix (Fin p) (Fin n) ℝ => columnMask C J) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  by_cases hj : j ∈ J
  · simpa only [columnMask, if_pos hj, Function.comp_def] using
      (continuous_apply j).comp (continuous_apply i)
  · simpa only [columnMask, if_neg hj] using
      (continuous_const : Continuous (fun _ : Matrix (Fin p) (Fin n) ℝ => (0 : ℝ)))

theorem columnMask_preservesZeroEntries {p n : ℕ}
    (C D : Matrix (Fin p) (Fin n) ℝ) (J : Finset (Fin n))
    (h : PreservesZeroEntries (columnMask C J) D) : PreservesZeroEntries C D := by
  intro i j hij
  apply h i j
  by_cases hj : j ∈ J <;> simp [columnMask, hj, hij]

/-- Synchronizing columns supported on at most one common coordinate keeps
the second group's rank, including an empty common support. -/
theorem replaceColumns_small_common_support_rank {p n : ℕ}
    (C D : Matrix (Fin p) (Fin n) ℝ) (J : Finset (Fin n))
    (O : Finset (Fin p)) (hO : O.card ≤ 1)
    (hC : ∀ j ∈ J, ∀ i, i ∉ O → C i j = 0)
    (hD : ∀ j ∈ J, ∀ i, i ∉ O → D i j = 0)
    (hzero : ∀ j ∈ J, ∀ i, C i j = 0 ↔ D i j = 0) :
    (replaceColumns C D J).rank = C.rank := by
  classical
  by_cases hne : O.Nonempty
  · obtain ⟨a, ha⟩ := hne
    apply replaceColumns_axis_rank C D J a
    · intro j hj i hi
      exact hC j hj i (fun hm => hi ((Finset.card_le_one.mp hO) i hm a ha))
    · intro j hj i hi
      exact hD j hj i (fun hm => hi ((Finset.card_le_one.mp hO) i hm a ha))
    · intro j hj
      exact hzero j hj a
  · have hz : O = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have heq : replaceColumns C D J = C := by
      ext i j
      by_cases hj : j ∈ J
      · have hi : i ∉ O := by rw [hz]; exact Finset.notMem_empty i
        simp only [replaceColumns, if_pos hj, hC j hj i hi, hD j hj i hi]
      · simp only [replaceColumns, if_neg hj]
    rw [heq]

/-- Use the first selected group on its labels, the second on its remaining
labels, and the baseline matrix elsewhere. -/
def mergeColumnGroups {p n : ℕ} (C D E : Matrix (Fin p) (Fin n) ℝ)
    (J K : Finset (Fin n)) : Matrix (Fin p) (Fin n) ℝ :=
  replaceColumns (replaceColumns C E K) D J

theorem mergeColumnGroups_first {p n : ℕ} (C D E : Matrix (Fin p) (Fin n) ℝ)
    (J K : Finset (Fin n)) (hD : ∀ i j, j ∉ J → D i j = 0) :
    columnMask (mergeColumnGroups C D E J K) J = D := by
  ext i j
  by_cases hj : j ∈ J
  · simp [columnMask, mergeColumnGroups, replaceColumns, hj]
  · simp [columnMask, hj, hD i j hj]

theorem mergeColumnGroups_second {p n : ℕ} (C D E : Matrix (Fin p) (Fin n) ℝ)
    (J K : Finset (Fin n)) (hE : ∀ i j, j ∉ K → E i j = 0) :
    columnMask (mergeColumnGroups C D E J K) K = replaceColumns E D (J ∩ K) := by
  ext i j
  by_cases hj : j ∈ J <;> by_cases hk : j ∈ K <;>
    simp [columnMask, mergeColumnGroups, replaceColumns, hj, hk, hE i j]

theorem mergeColumnGroups_self {p n : ℕ} (C : Matrix (Fin p) (Fin n) ℝ)
    (J K : Finset (Fin n)) : mergeColumnGroups C (columnMask C J) (columnMask C K) J K = C := by
  ext i j
  by_cases hj : j ∈ J <;> by_cases hk : j ∈ K <;>
    simp [columnMask, mergeColumnGroups, replaceColumns, hj, hk]

#print axioms replaceColumns_small_common_support_rank

end Papers.RationalityTen.FixedCoordinateFlagDensity

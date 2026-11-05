module
public import Papers.RelativeKernelMatrixDensity

@[expose] public section
noncomputable section

open Matrix Module Set Filter Topology
open scoped BigOperators

namespace Papers.RationalityTen.FixedCoordinateFlagDensity

open ChirotopeDensity PlaneRationalization

/-- Replacing each column by a nonzero scalar multiple preserves its actual
column span, and hence its matrix rank. -/
theorem rank_eq_of_column_rescaling {p n : ℕ}
    (C D : Matrix (Fin p) (Fin n) ℝ)
    (h : ∀ j, ∃ t : ℝ, t ≠ 0 ∧ D.col j = t • C.col j) :
    D.rank = C.rank := by
  have hspan : Submodule.span ℝ (Set.range D.col) =
      Submodule.span ℝ (Set.range C.col) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      obtain ⟨t, ht, hj⟩ := h j
      rw [hj]
      exact Submodule.smul_mem _ t (Submodule.subset_span (Set.mem_range_self j))
    · apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      obtain ⟨t, ht, hj⟩ := h j
      have heq : C.col j = t⁻¹ • D.col j := by
        rw [hj, smul_smul, inv_mul_cancel₀ ht, one_smul]
      rw [heq]
      exact Submodule.smul_mem _ t⁻¹ (Submodule.subset_span (Set.mem_range_self j))
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols, hspan]

/-- Copy the indicated labelled columns from a second matrix. -/
def replaceColumns {p n : ℕ} (C D : Matrix (Fin p) (Fin n) ℝ)
    (J : Finset (Fin n)) : Matrix (Fin p) (Fin n) ℝ :=
  fun i j => if j ∈ J then D i j else C i j

/-- When common columns lie on one coordinate axis, their nonzero scalar
values may be synchronized without changing either group's column rank.
The zero-pattern equivalence includes originally zero common columns. -/
theorem replaceColumns_axis_rank {p n : ℕ}
    (C D : Matrix (Fin p) (Fin n) ℝ) (J : Finset (Fin n)) (a : Fin p)
    (hC : ∀ j ∈ J, ∀ i, i ≠ a → C i j = 0)
    (hD : ∀ j ∈ J, ∀ i, i ≠ a → D i j = 0)
    (hzero : ∀ j ∈ J, C a j = 0 ↔ D a j = 0) :
    (replaceColumns C D J).rank = C.rank := by
  apply rank_eq_of_column_rescaling C
  intro j
  by_cases hj : j ∈ J
  · by_cases hc : C a j = 0
    · refine ⟨1, one_ne_zero, ?_⟩
      ext i
      by_cases hi : i = a
      · subst i
        simp [replaceColumns, hj, hc, (hzero j hj).mp hc]
      · simp [replaceColumns, hj, hC j hj i hi, hD j hj i hi]
    · have hd : D a j ≠ 0 := mt (hzero j hj).mpr hc
      refine ⟨D a j / C a j, div_ne_zero hd hc, ?_⟩
      ext i
      by_cases hi : i = a
      · subst i
        simp [replaceColumns, hj, div_mul_cancel₀ _ hc]
      · simp [replaceColumns, hj, hC j hj i hi, hD j hj i hi]
  · refine ⟨1, one_ne_zero, ?_⟩
    ext i
    simp [replaceColumns, hj]

/-- Column copying preserves a shared annihilator exactly. -/
theorem replaceColumns_mul_eq_zero {m p n : ℕ}
    (A : Matrix (Fin m) (Fin p) ℝ) (C D : Matrix (Fin p) (Fin n) ℝ)
    (J : Finset (Fin n)) (hC : A * C = 0)
    (hD : ∀ j ∈ J, A.mulVec (D.col j) = 0) :
    A * replaceColumns C D J = 0 := by
  ext i j
  by_cases hj : j ∈ J
  · simpa [replaceColumns, Matrix.mul_apply, Matrix.mulVec, dotProduct, hj] using
      congrFun (hD j hj) i
  · simpa [replaceColumns, Matrix.mul_apply, hj] using congrFun (congrFun hC i) j

/-- Rational coordinates and prescribed zeros survive synchronizing columns. -/
theorem replaceColumns_rational {p n : ℕ}
    (C D : Matrix (Fin p) (Fin n) ℝ) (J : Finset (Fin n))
    (hC : RationalCoordinates C) (hD : RationalCoordinates D) :
    RationalCoordinates (replaceColumns C D J) := by
  intro i j
  by_cases hj : j ∈ J
  · simpa only [replaceColumns, if_pos hj] using hD i j
  · simpa only [replaceColumns, if_neg hj] using hC i j

theorem replaceColumns_preservesZeroEntries {p n : ℕ}
    (B C D : Matrix (Fin p) (Fin n) ℝ) (J : Finset (Fin n))
    (hC : PreservesZeroEntries B C) (hD : PreservesZeroEntries B D) :
    PreservesZeroEntries B (replaceColumns C D J) := by
  intro i j hij
  by_cases hj : j ∈ J
  · simpa only [replaceColumns, if_pos hj] using hD i j hij
  · simpa only [replaceColumns, if_neg hj] using hC i j hij

theorem replaceColumns_continuous {p n : ℕ} (J : Finset (Fin n)) :
    Continuous (fun z : Matrix (Fin p) (Fin n) ℝ × Matrix (Fin p) (Fin n) ℝ =>
      replaceColumns z.1 z.2 J) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  by_cases hj : j ∈ J
  · simpa only [replaceColumns, if_pos hj, Function.comp_def] using
      (continuous_apply j).comp ((continuous_apply i).comp continuous_snd)
  · simpa only [replaceColumns, if_neg hj, Function.comp_def] using
      (continuous_apply j).comp ((continuous_apply i).comp continuous_fst)

#print axioms replaceColumns_axis_rank
#print axioms replaceColumns_mul_eq_zero

end Papers.RationalityTen.FixedCoordinateFlagDensity

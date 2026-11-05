module
public import Papers.RelativeRankOneDensity
public import Papers.CoordinateAxisColumnGluing

@[expose] public section
noncomputable section

open Matrix Module Set Filter Topology
open scoped BigOperators

namespace Papers.RationalityTen.FixedCoordinateFlagDensity

open ChirotopeDensity PlaneRationalization

/-- Retain one disjoint labelled group of columns and zero the others. -/
def groupColumnMask {p n k : ℕ} (g : Fin n → Option (Fin k))
    (C : Matrix (Fin p) (Fin n) ℝ) (a : Fin k) : Matrix (Fin p) (Fin n) ℝ :=
  fun i j => if g j = some a then C i j else 0

/-- Synchronize each assigned column to a scalar multiple of its group's
representative; unassigned columns are retained literally. -/
def synchronizeColumns {p n k : ℕ} (g : Fin n → Option (Fin k))
    (rep : Fin k → Fin n) (C : Matrix (Fin p) (Fin n) ℝ) (w : Fin n → ℝ) :
    Matrix (Fin p) (Fin n) ℝ :=
  fun i j => match g j with
    | none => C i j
    | some a => w j * C i (rep a)

theorem synchronizeColumns_self {p n k : ℕ}
    (g : Fin n → Option (Fin k)) (rep : Fin k → Fin n)
    (C : Matrix (Fin p) (Fin n) ℝ) (w : Fin n → ℝ)
    (hfactor : ∀ j a, g j = some a → ∀ i, C i j = w j * C i (rep a)) :
    synchronizeColumns g rep C w = C := by
  ext i j
  cases h : g j with
  | none => simp [synchronizeColumns, h]
  | some a => simpa only [synchronizeColumns, h] using (hfactor j a h i).symm

theorem synchronizeColumns_continuous {p n k : ℕ}
    (g : Fin n → Option (Fin k)) (rep : Fin k → Fin n) :
    Continuous (fun z : Matrix (Fin p) (Fin n) ℝ × (Fin n → ℝ) =>
      synchronizeColumns g rep z.1 z.2) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  cases h : g j with
  | none =>
      simpa only [synchronizeColumns, h, Function.comp_def] using
        (continuous_apply j).comp ((continuous_apply i).comp continuous_fst)
  | some a =>
      simp only [synchronizeColumns, h]
      exact continuous_mul.comp
        (((continuous_apply j).comp continuous_snd).prodMk
          ((continuous_apply (rep a)).comp ((continuous_apply i).comp continuous_fst)))

theorem groupColumnMask_continuous {p n k : ℕ}
    (g : Fin n → Option (Fin k)) (a : Fin k) :
    Continuous (fun C : Matrix (Fin p) (Fin n) ℝ => groupColumnMask g C a) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  by_cases h : g j = some a
  · simpa only [groupColumnMask, if_pos h, Function.comp_def] using
      ((continuous_apply j).comp (continuous_apply i) :
        Continuous (fun C : Matrix (Fin p) (Fin n) ℝ => C i j))
  · simpa only [groupColumnMask, if_neg h] using
      (continuous_const : Continuous (fun _ : Matrix (Fin p) (Fin n) ℝ => (0 : ℝ)))

theorem synchronizeColumns_rational {p n k : ℕ}
    (g : Fin n → Option (Fin k)) (rep : Fin k → Fin n)
    (C : Matrix (Fin p) (Fin n) ℝ) (w : Fin n → ℝ)
    (hC : RationalCoordinates C) (hw : ∀ j, RatScalar (w j)) :
    RationalCoordinates (synchronizeColumns g rep C w) := by
  intro i j
  cases h : g j with
  | none => simpa only [synchronizeColumns, h] using hC i j
  | some a => simpa only [synchronizeColumns, h] using (hw j).mul (hC i (rep a))

theorem synchronizeColumns_preserves_zeros {p n k : ℕ}
    (g : Fin n → Option (Fin k)) (rep : Fin k → Fin n)
    (C D : Matrix (Fin p) (Fin n) ℝ) (w z : Fin n → ℝ)
    (hfactor : ∀ j a, g j = some a → ∀ i, C i j = w j * C i (rep a))
    (hD : PreservesZeroEntries C D) (hz : ∀ j, w j = 0 → z j = 0) :
    PreservesZeroEntries C (synchronizeColumns g rep D z) := by
  intro i j hij
  cases h : g j with
  | none => simpa only [synchronizeColumns, h] using hD i j hij
  | some a =>
      have hprod : w j * C i (rep a) = 0 := (hfactor j a h i).symm.trans hij
      rcases mul_eq_zero.mp hprod with hw | hc
      · simp only [synchronizeColumns, h, hz j hw, zero_mul]
      · simp only [synchronizeColumns, h, hD i (rep a) hc, mul_zero]

/-- Synchronization never enlarges the original column span. -/
theorem synchronizeColumns_rank_le {p n k : ℕ}
    (g : Fin n → Option (Fin k)) (rep : Fin k → Fin n)
    (C : Matrix (Fin p) (Fin n) ℝ) (w : Fin n → ℝ) :
    (synchronizeColumns g rep C w).rank ≤ C.rank := by
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
  apply Submodule.finrank_mono
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  cases h : g j with
  | none =>
      have heq : (synchronizeColumns g rep C w).col j = C.col j := by
        ext i
        simp [synchronizeColumns, Matrix.col_apply, h]
      rw [heq]
      exact Submodule.subset_span (Set.mem_range_self j)
  | some a =>
      have heq : (synchronizeColumns g rep C w).col j = w j • C.col (rep a) := by
        ext i
        simp [synchronizeColumns, Matrix.col_apply, h, smul_eq_mul]
      rw [heq]
      exact Submodule.smul_mem _ (w j) (Submodule.subset_span (Set.mem_range_self (rep a)))

/-- Every synchronized group has column rank at most one. -/
theorem synchronizeColumns_group_rank_le_one {p n k : ℕ}
    (g : Fin n → Option (Fin k)) (rep : Fin k → Fin n)
    (C : Matrix (Fin p) (Fin n) ℝ) (w : Fin n → ℝ) (a : Fin k) :
    (groupColumnMask g (synchronizeColumns g rep C w) a).rank ≤ 1 := by
  rw [Matrix.rank_eq_finrank_span_cols]
  have hspan : Submodule.span ℝ
      (Set.range (groupColumnMask g (synchronizeColumns g rep C w) a).col) ≤
      Submodule.span ℝ ({C.col (rep a)} : Set (Fin p → ℝ)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    by_cases h : g j = some a
    · have heq : (groupColumnMask g (synchronizeColumns g rep C w) a).col j =
          w j • C.col (rep a) := by
        ext i
        simp [groupColumnMask, synchronizeColumns, Matrix.col_apply, h, smul_eq_mul]
      rw [heq]
      exact Submodule.smul_mem _ (w j) (Submodule.subset_span (Set.mem_singleton _))
    · have heq : (groupColumnMask g (synchronizeColumns g rep C w) a).col j = 0 := by
        ext i
        simp [groupColumnMask, Matrix.col_apply, h]
      rw [heq]
      exact Submodule.zero_mem _
  exact (Submodule.finrank_mono hspan).trans
    ((finrank_span_le_card ({C.col (rep a)} : Set (Fin p → ℝ))).trans (by simp))

/-- An original independent-row minor gives the lower rank bound nearby. -/
theorem rowKernelChart_rank_le {p n : ℕ}
    (C : Matrix (Fin p) (Fin n) ℝ) (B : RowKernelChart C)
    (D : Matrix (Fin p) (Fin n) ℝ)
    (h : LinearIndependent ℝ (fun i => D (B.rows i))) : C.rank ≤ D.rank := by
  have hi := h.rank_matrix
  have hl := Matrix.rank_submatrix_le D B.rows id
  change (D.submatrix B.rows id).rank = Fintype.card (Fin B.rank) at hi
  simp only [Fintype.card_fin] at hi
  rw [hi, ← B.rank_eq] at hl
  exact hl

/-- Ordinary rational matrix density can simultaneously preserve any finite
family of disjoint rank-one column groups. The construction only rescales
representative columns, so it preserves the total rank and every zero entry.
This is the relative refinement needed in the golden exceptional case. -/
theorem rational_density_with_rank_one_column_groups {p n k : ℕ}
    (g : Fin n → Option (Fin k)) (rep : Fin k → Fin n)
    (C : Matrix (Fin p) (Fin n) ℝ) (w : Fin n → ℝ)
    (hfactor : ∀ j a, g j = some a → ∀ i, C i j = w j * C i (rep a))
    (hgroups : ∀ a, (groupColumnMask g C a).rank = 1)
    (hdense : C ∈ closure {D : Matrix (Fin p) (Fin n) ℝ |
      RationalCoordinates D ∧ D.rank = C.rank ∧ PreservesZeroEntries C D}) :
    C ∈ closure {D : Matrix (Fin p) (Fin n) ℝ |
      RationalCoordinates D ∧ D.rank = C.rank ∧ PreservesZeroEntries C D ∧
      ∀ a, (groupColumnMask g D a).rank = 1} := by
  classical
  let S : Set (Matrix (Fin p) (Fin n) ℝ) :=
    {D | RationalCoordinates D ∧ D.rank = C.rank ∧ PreservesZeroEntries C D}
  let W : Set (Fin n → ℝ) := {z | (∀ j, RatScalar (z j)) ∧ ∀ j, w j = 0 → z j = 0}
  let F : Matrix (Fin p) (Fin n) ℝ × (Fin n → ℝ) → Matrix (Fin p) (Fin n) ℝ :=
    fun z => synchronizeColumns g rep z.1 z.2
  have hF : Continuous F := synchronizeColumns_continuous g rep
  have hbase : F (C, w) = C := synchronizeColumns_self g rep C w hfactor
  have hprod : (C, w) ∈ closure (S ×ˢ W) := by
    rw [closure_prod_eq]
    exact ⟨hdense, rational_vector_zero_pattern_density w⟩
  obtain ⟨B⟩ := exists_rowKernelChart C
  let BG : (a : Fin k) → RowKernelChart (groupColumnMask g C a) :=
    fun a => Classical.choice (exists_rowKernelChart _)
  have hmain : ∀ᶠ z in 𝓝 (C, w), LinearIndependent ℝ (fun i => F z (B.rows i)) := by
    have ht : Tendsto F (𝓝 (C, w)) (𝓝 C) := by
      simpa only [hbase] using (hF.continuousAt (x := (C, w))).tendsto
    exact ht.eventually B.eventually_independent
  have hgroup : ∀ᶠ z in 𝓝 (C, w), ∀ a,
      LinearIndependent ℝ (fun i => groupColumnMask g (F z) a ((BG a).rows i)) := by
    apply eventually_all.mpr
    intro a
    have hc := (groupColumnMask_continuous g a).comp hF
    have ht : Tendsto (fun z => groupColumnMask g (F z) a)
        (𝓝 (C, w)) (𝓝 (groupColumnMask g C a)) := by
      simpa only [Function.comp_def, hbase] using (hc.continuousAt (x := (C, w))).tendsto
    exact ht.eventually (BG a).eventually_independent
  have hcl := mem_closure_image (hF.continuousAt (x := (C, w)))
    (mem_closure_inter_of_eventually hprod (hmain.and hgroup))
  rw [hbase] at hcl
  apply closure_mono (s := F '' _) ?_ hcl
  rintro _ ⟨⟨D, z⟩, ⟨⟨hD, hz⟩, hgood⟩, rfl⟩
  have hlow : C.rank ≤ (F (D, z)).rank :=
    rowKernelChart_rank_le C B _ hgood.1
  have hhigh : (F (D, z)).rank ≤ C.rank :=
    (synchronizeColumns_rank_le g rep D z).trans hD.2.1.le
  refine ⟨synchronizeColumns_rational g rep D z hD.1 hz.1,
    Nat.le_antisymm hhigh hlow,
    synchronizeColumns_preserves_zeros g rep C D w z hfactor hD.2.2 hz.2, ?_⟩
  intro a
  have hlo := rowKernelChart_rank_le (groupColumnMask g C a) (BG a)
    (groupColumnMask g (F (D, z)) a) (hgood.2 a)
  rw [hgroups a] at hlo
  exact Nat.le_antisymm (synchronizeColumns_group_rank_le_one g rep D z a) hlo

#print axioms rational_density_with_rank_one_column_groups

end Papers.RationalityTen.FixedCoordinateFlagDensity

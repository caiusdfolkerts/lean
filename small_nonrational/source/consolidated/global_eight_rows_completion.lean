module
public import Papers.RankOneColumnGroups
public import Papers.MatrixSupportCounts
public import Papers.RelativeKernelRankCases
public import Papers.ColumnGroupGluing
public import Mathlib.Tactic.FinCases
public import Papers.ActualReducedRelationData
public import Papers.ReducedFacetReconstruction
public import Consolidated.SelectedRankGeometry
public import Papers.RationalAnnihilatorDensity
public import Papers.TwoSmallColumnGroupsDensity
public import Mathlib.Data.Fintype.EquivFin
public import Papers.EightRelationRowsAssembly

/-! Global Proposition 8 assembly. Original file scopes are preserved. -/

section BundlePart0
/- Original module: Papers.OmittedSupportCounting. -/

@[expose] public section
noncomputable section

open Matrix Module Set
open scoped BigOperators

namespace Papers.RationalityTen.FixedCoordinateFlagDensity

open ChirotopeDensity

/-- A positive kernel combination supported on a column group cannot have
exactly one nonzero column in that group. -/
theorem positive_kernel_has_two_active_columns {s n : ℕ}
    (C : Matrix (Fin s) (Fin n) ℝ) (J : Finset (Fin n)) (w : Fin n → ℝ)
    (hker : C.mulVec w = 0) (hpos : ∀ j ∈ J, 0 < w j)
    (hzero : ∀ j, j ∉ J → w j = 0)
    (hne : ∃ j ∈ J, j ∈ activeColumns C) :
    ∃ j ∈ J, ∃ k ∈ J, j ∈ activeColumns C ∧ k ∈ activeColumns C ∧ j ≠ k := by
  classical
  obtain ⟨j, hj, hja⟩ := hne
  obtain ⟨i, hij⟩ := (mem_activeColumns C j).mp hja
  have hk : ∃ k ∈ J, k ∈ activeColumns C ∧ j ≠ k := by
    by_contra h
    have hz : C i j * w j = 0 := by
      have hi := congrFun hker i
      change (∑ k, C i k * w k) = 0 at hi
      rw [Finset.sum_eq_single j] at hi
      · exact hi
      · intro k _ hkj
        by_cases hkJ : k ∈ J
        · have hkzero : C i k = 0 := by
            by_contra hik
            exact h ⟨k, hkJ, (mem_activeColumns C k).mpr ⟨i, hik⟩, Ne.symm hkj⟩
          rw [hkzero, zero_mul]
        · rw [hzero k hkJ, mul_zero]
      · exact fun hn => (hn (Finset.mem_univ j)).elim
    exact (mul_ne_zero hij (ne_of_gt (hpos j hj))) hz
  obtain ⟨k, hkJ, hka, hne⟩ := hk
  exact ⟨j, hj, k, hkJ, hja, hka, hne⟩

theorem active_support_eq_of_four {s n : ℕ}
    (C : Matrix (Fin s) (Fin n) ℝ) (O : Finset (Fin s)) (hO : O.card ≤ 4)
    (hfour : ∀ j ∈ activeColumns C, 4 ≤ (columnSupport C j).card)
    (j : Fin n) (hj : j ∈ activeColumns C)
    (hsupport : ∀ i, i ∉ O → C i j = 0) : columnSupport C j = O := by
  have hsub : columnSupport C j ⊆ O := by
    intro i hi
    by_contra hn
    exact (Finset.mem_filter.mp hi).2 (hsupport i hn)
  apply Finset.eq_of_subset_of_card_le hsub
  have h := hfour j hj
  omega

/-- With at most nine active columns, a repeated nonzero support leaves at
most eight distinct supports. -/
theorem support_image_card_le_eight_of_repeat {s n : ℕ}
    (C : Matrix (Fin s) (Fin n) ℝ) (hcard : (activeColumns C).card ≤ 9)
    (j k : Fin n) (hj : j ∈ activeColumns C) (hk : k ∈ activeColumns C)
    (hne : j ≠ k) (hsame : columnSupport C j = columnSupport C k) :
    ((activeColumns C).image (columnSupport C)).card ≤ 8 := by
  have hle := Finset.card_image_le (s := activeColumns C) (f := columnSupport C)
  have hneq : ((activeColumns C).image (columnSupport C)).card ≠ (activeColumns C).card := by
    intro h
    have hinj := Finset.card_image_iff.mp h
    exact hne (hinj hj hk hsame)
  omega

/-- The supporting-form argument excludes the full nine-flat obstruction
in arbitrary vertex count. It uses either thirty-two nonzeros directly, or
thirty-six nonzeros plus an occupied four-coordinate outside group. -/
theorem at_most_eight_column_supports_of_positive_kernel {s n : ℕ}
    (C : Matrix (Fin s) (Fin n) ℝ)
    (hfour : ∀ j ∈ activeColumns C, 4 ≤ (columnSupport C j).card)
    (hnnz : totalNonzeros C ≤ 36)
    (J : Finset (Fin n)) (O : Finset (Fin s)) (hO : O.card ≤ 4)
    (hsupport : ∀ j ∈ J, ∀ i, i ∉ O → C i j = 0)
    (hrow : ∀ i ∈ O, ∃ j ∈ J, C i j ≠ 0)
    (hempty : O = ∅ → totalNonzeros C ≤ 32)
    (w : Fin n → ℝ) (hker : C.mulVec w = 0)
    (hpos : ∀ j ∈ J, 0 < w j) (hzero : ∀ j, j ∉ J → w j = 0) :
    ((activeColumns C).image (columnSupport C)).card ≤ 8 := by
  classical
  have hcount := four_mul_activeColumns_le C hfour
  by_cases hne : O.Nonempty
  · obtain ⟨i, hi⟩ := hne
    obtain ⟨j, hj, hij⟩ := hrow i hi
    have hactive : j ∈ activeColumns C := (mem_activeColumns C j).mpr ⟨i, hij⟩
    obtain ⟨j, hj, k, hk, hja, hka, hjk⟩ := positive_kernel_has_two_active_columns
      C J w hker hpos hzero ⟨j, hj, hactive⟩
    apply support_image_card_le_eight_of_repeat C (by omega) j k hja hka hjk
    exact (active_support_eq_of_four C O hO hfour j hja (hsupport j hj)).trans
      (active_support_eq_of_four C O hO hfour k hka (hsupport k hk)).symm
  · have hz : O = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hsmall := hempty hz
    exact (Finset.card_image_le).trans (by omega)

/-- A support catalogue of nine four-element sets necessarily contains one
that is unused by every column, when there are at most eight active supports. -/
theorem omitted_four_support_of_image_card_le_eight {s n : ℕ}
    (C : Matrix (Fin s) (Fin n) ℝ)
    (hcard : ((activeColumns C).image (columnSupport C)).card ≤ 8)
    (L : Finset (Finset (Fin s))) (hL : L.card = 9)
    (hfour : ∀ S ∈ L, S.card = 4) :
    ∃ S ∈ L, ∀ j, columnSupport C j ≠ S := by
  classical
  by_contra h
  have hsub : L ⊆ (activeColumns C).image (columnSupport C) := by
    intro S hS
    have hex : ∃ j, columnSupport C j = S := by
      by_contra hn
      exact h ⟨S, hS, fun j hj => hn ⟨j, hj⟩⟩
    obtain ⟨j, hj⟩ := hex
    have hne : S.Nonempty := Finset.card_pos.mp (by rw [hfour S hS]; decide)
    obtain ⟨i, hi⟩ := hne
    have hij : C i j ≠ 0 := by
      rw [← hj] at hi
      exact (Finset.mem_filter.mp hi).2
    exact Finset.mem_image.mpr ⟨j, (mem_activeColumns C j).mpr ⟨i, hij⟩, hj⟩
  have hle := Finset.card_le_card hsub
  omega

#print axioms at_most_eight_column_supports_of_positive_kernel

end Papers.RationalityTen.FixedCoordinateFlagDensity

end
end
end BundlePart0

section BundlePart1
/- Original module: Papers.RankAtMostOneColumnGroups. -/

@[expose] public section
noncomputable section
open Matrix Module Set Filter Topology
open scoped BigOperators
namespace Papers.RationalityTen.FixedCoordinateFlagDensity
open ChirotopeDensity PlaneRationalization

/-- Synchronization also preserves groups of rank zero: their original
zero entries force the entire group to remain zero. -/
theorem rational_density_with_rank_at_most_one_column_groups {p n k : ℕ}
    (g : Fin n → Option (Fin k)) (rep : Fin k → Fin n)
    (C : Matrix (Fin p) (Fin n) ℝ) (w : Fin n → ℝ)
    (hfactor : ∀ j a, g j = some a → ∀ i, C i j = w j * C i (rep a))
    (hgroups : ∀ a, (groupColumnMask g C a).rank ≤ 1)
    (hdense : C ∈ closure {D : Matrix (Fin p) (Fin n) ℝ |
      RationalCoordinates D ∧ D.rank = C.rank ∧ PreservesZeroEntries C D}) :
    C ∈ closure {D : Matrix (Fin p) (Fin n) ℝ |
      RationalCoordinates D ∧ D.rank = C.rank ∧ PreservesZeroEntries C D ∧
      ∀ a, (groupColumnMask g D a).rank = (groupColumnMask g C a).rank} := by
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
  by_cases hzero : (groupColumnMask g C a).rank = 0
  · have hmask := matrix_eq_zero_of_rank_zero (groupColumnMask g C a) hzero
    have hpres := synchronizeColumns_preserves_zeros g rep C D w z hfactor hD.2.2 hz.2
    have hnew : groupColumnMask g (F (D, z)) a = 0 := by
      ext i j
      by_cases hj : g j = some a
      · have hCij : C i j = 0 := by
          have h := congrFun (congrFun hmask i) j
          simpa only [groupColumnMask, if_pos hj, Matrix.zero_apply] using h
        change (if g j = some a then F (D, z) i j else 0) = 0
        rw [if_pos hj]
        exact hpres i j hCij
      · simp only [groupColumnMask, if_neg hj, Matrix.zero_apply]
    rw [hnew, Matrix.rank_zero, hzero]
  · have hone : (groupColumnMask g C a).rank = 1 := by have h := hgroups a; omega
    rw [hone] at hlo ⊢
    exact Nat.le_antisymm (synchronizeColumns_group_rank_le_one g rep D z a) hlo


/-- Ordinary rational matrix density preserves the ranks of any finite
family of disjoint column groups whose original ranks are at most one.
Zero groups, empty matrices, and unassigned columns are all included. -/
theorem rational_density_preserving_rank_at_most_one_groups {p n k : ℕ}
    (g : Fin n → Option (Fin k)) (C : Matrix (Fin p) (Fin n) ℝ)
    (hgroups : ∀ a, (groupColumnMask g C a).rank ≤ 1)
    (hdense : C ∈ closure {D : Matrix (Fin p) (Fin n) ℝ |
      RationalCoordinates D ∧ D.rank = C.rank ∧ PreservesZeroEntries C D}) :
    C ∈ closure {D : Matrix (Fin p) (Fin n) ℝ |
      RationalCoordinates D ∧ D.rank = C.rank ∧ PreservesZeroEntries C D ∧
      ∀ a, (groupColumnMask g D a).rank = (groupColumnMask g C a).rank} := by
  classical
  by_cases hn : n = 0
  · subst n
    apply subset_closure
    refine ⟨?_, rfl, ?_, fun _ => rfl⟩
    · intro i j
      exact Fin.elim0 j
    · intro i j _
      exact Fin.elim0 j
  have hnpos : 0 < n := by omega
  have hex : ∀ a : Fin k, ∃ rep : Fin n,
      ∀ j, g j = some a → ∃ t : ℝ, ∀ i, C i j = t * C i rep := by
    intro a
    by_cases hz : (groupColumnMask g C a).rank = 0
    · have hm := matrix_eq_zero_of_rank_zero (groupColumnMask g C a) hz
      refine ⟨⟨0, hnpos⟩, ?_⟩
      intro j hj
      refine ⟨0, ?_⟩
      intro i
      have h := congrFun (congrFun hm i) j
      have hij : C i j = 0 := by
        simpa only [groupColumnMask, if_pos hj, Matrix.zero_apply] using h
      rw [hij, zero_mul]
    · have ho : (groupColumnMask g C a).rank = 1 := by have h := hgroups a; omega
      obtain ⟨rep, _, _, hf⟩ := rank_one_group_factorization g C a ho
      exact ⟨rep, hf⟩
  choose rep hfactor using hex
  have hcoeff : ∀ j, ∃ t : ℝ, ∀ a, g j = some a → ∀ i, C i j = t * C i (rep a) := by
    intro j
    cases h : g j with
    | none =>
        refine ⟨0, ?_⟩
        intro a ha
        cases ha
    | some a =>
        obtain ⟨t, ht⟩ := hfactor a j h
        refine ⟨t, ?_⟩
        intro b hb
        have hab : a = b := Option.some.inj hb
        subst b
        exact ht
  choose w hw using hcoeff
  exact rational_density_with_rank_at_most_one_column_groups g rep C w hw hgroups hdense

#print axioms rational_density_preserving_rank_at_most_one_groups

end Papers.RationalityTen.FixedCoordinateFlagDensity

end
end
end BundlePart1

section BundlePart2
/- Original module: Papers.TwoRankOneGroupsDensity. -/

@[expose] public section
noncomputable section

open Matrix Module Set Filter Topology
open scoped BigOperators

namespace Papers.RationalityTen.FixedCoordinateFlagDensity

open ChirotopeDensity PlaneRationalization

/-- Two column groups of rank at most one can be synchronized even when
labels overlap, provided their common original columns are zero. This is
exactly the golden exceptional situation forced by four-entry support and
at most one common outside row. -/
theorem rational_density_two_rank_at_most_one_groups {s n : ℕ}
    (C : Matrix (Fin s) (Fin n) ℝ) (J K : Finset (Fin n))
    (hJ : subsetRank C.col J ≤ 1) (hK : subsetRank C.col K ≤ 1)
    (hzero : ∀ j ∈ J ∩ K, ∀ i, C i j = 0)
    (hdense : C ∈ closure {D : Matrix (Fin s) (Fin n) ℝ |
      RationalCoordinates D ∧ D.rank = C.rank ∧ PreservesZeroEntries C D}) :
    C ∈ closure {D : Matrix (Fin s) (Fin n) ℝ |
      RationalCoordinates D ∧ D.rank = C.rank ∧ PreservesZeroEntries C D ∧
      subsetRank D.col J = subsetRank C.col J ∧
      subsetRank D.col K = subsetRank C.col K} := by
  classical
  let g : Fin n → Option (Fin 2) := fun j =>
    if j ∈ J then some 0 else if j ∈ K then some 1 else none
  have hfirst (D : Matrix (Fin s) (Fin n) ℝ) :
      groupColumnMask g D 0 = columnMask D J := by
    ext i j
    by_cases hj : j ∈ J <;> by_cases hk : j ∈ K <;>
      simp [g, groupColumnMask, columnMask, hj, hk]
  have hsecond (D : Matrix (Fin s) (Fin n) ℝ)
      (hz : ∀ j ∈ J ∩ K, ∀ i, D i j = 0) :
      groupColumnMask g D 1 = columnMask D K := by
    ext i j
    by_cases hj : j ∈ J <;> by_cases hk : j ∈ K
    · simp [g, groupColumnMask, columnMask, hj, hk, hz j (Finset.mem_inter.mpr ⟨hj, hk⟩) i]
    · simp [g, groupColumnMask, columnMask, hj, hk]
    · simp [g, groupColumnMask, columnMask, hj, hk]
    · simp [g, groupColumnMask, columnMask, hj, hk]
  have hgroups : ∀ a, (groupColumnMask g C a).rank ≤ 1 := by
    intro a
    fin_cases a
    · change (groupColumnMask g C 0).rank ≤ 1
      rw [hfirst C, columnMask_rank]
      exact hJ
    · change (groupColumnMask g C 1).rank ≤ 1
      rw [hsecond C hzero, columnMask_rank]
      exact hK
  have hc := rational_density_preserving_rank_at_most_one_groups g C hgroups hdense
  apply closure_mono ?_ hc
  intro D hD
  have hzD : ∀ j ∈ J ∩ K, ∀ i, D i j = 0 :=
    fun j hj i => hD.2.2.1 i j (hzero j hj i)
  refine ⟨hD.1, hD.2.1, hD.2.2.1, ?_, ?_⟩
  · have h := hD.2.2.2 0
    rw [hfirst D, hfirst C, columnMask_rank, columnMask_rank] at h
    exact h
  · have h := hD.2.2.2 1
    rw [hsecond D hzD, hsecond C hzero, columnMask_rank, columnMask_rank] at h
    exact h

#print axioms rational_density_two_rank_at_most_one_groups

end Papers.RationalityTen.FixedCoordinateFlagDensity

end
end
end BundlePart2

section BundlePart3
/- Original module: Papers.ActualReducedReconstruction. -/

@[expose] public section
noncomputable section

open Set Matrix
open LeanEval.Geometry.PlatonicClassification
open Papers.Polytopes

namespace Papers.RationalityTen.ChirotopeDensity

/-- The reduced matrix density obligation, including exactly the selected
 outside-column ranks used in reconstruction. -/
def ReducedFacetMatrixData.Dense {n : ℕ} {p : Fin n → Fin 5 → ℝ} {g : ℤ}
    (D : ReducedFacetMatrixData p g) : Prop :=
  D.matrix ∈ closure {C' : Matrix (Fin D.rowCount) (Fin n) ℝ |
    RationalCoordinates C' ∧ C'.rank = D.matrix.rank ∧ PreservesZeroEntries D.matrix C' ∧
    ∀ a, subsetRank D.matrix.col (D.masks a)ᶜ = subsetRank C'.col (D.masks a)ᶜ}

/-- Apply the exact reduced-coordinate reconstruction to actual extreme
 vertices and ordinary face-order realization density. -/
theorem rationallyApproximable_of_reducedFacetMatrixData_density {n : ℕ}
    (Q : ConvexPolytope 4) (hQ : Q.IsFullDim) (e : Fin n ≃ Q.vertices)
    (g : ℤ) (D : ReducedFacetMatrixData (vertexCoordinates Q e) g) (hD : D.Dense) :
    RationallyApproximable Q := by
  have hh := FixedCoordinateFlagDensity.rational_polytope_density_from_reduced_relations
    D.matrix (vertexCoordinates Q e) (vertexCoordinates_spans Q e hQ) (fun _ => rfl)
    D.annihilates D.exceptionCount_le D.masks D.masks_injective D.masks_facets
    D.spans_other_facets hD
  have ho := ordinary_density_of_homogeneous_density (ordinaryVertexCoordinates Q e)
    (by simpa only [ordinaryVertexCoordinates_homogeneous] using hh)
  apply rationallyApproximable_of_coordinate_density Q e
  apply closure_mono ?_ ho
  intro q hq
  exact ⟨hq.1,hq.2.2⟩

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart3

section BundlePart4
/- Original module: Papers.GoldenReducedMatrixDensity. -/

@[expose] public section
noncomputable section

open Matrix Module Set Filter Topology
open scoped BigOperators

namespace Papers.RationalityTen.FixedCoordinateFlagDensity

open ChirotopeDensity PlaneRationalization
open MatroidChecked.MatrixClassificationCore MatroidChecked.GoldenSelectedRanks
open MatroidChecked.GoldenOmissionAssembly

/-- The omitted-flat reconstruction is valid for arbitrary column count.
At most eight distinct active supports exclude one of the nine exceptional
four-flats, exactly as in the nine-column special instance. -/
theorem golden_matrix_density_of_few_supports {n : ℕ}
    (C : Matrix (Fin 8) (Fin n) ℝ) (hgolden : GoldenIntrinsic C)
    (hcard : ((activeColumns C).image (columnSupport C)).card ≤ 8) :
    C ∈ closure {D : Matrix (Fin 8) (Fin n) ℝ |
      RationalCoordinates D ∧ D.rank = C.rank ∧ PreservesZeroEntries C D} := by
  obtain ⟨u, E, hu, hE, ⟨σ, hσ⟩, hC⟩ := hgolden
  have hgu := golden_of_catalogue u σ hσ
  let L := goldenFlats u
  let M := L.image (fun S => Sᶜ)
  have hM : M.card = 9 := by
    rw [Finset.card_image_of_injective _ compl_injective]
    exact hgu.flats_card
  have hfour : ∀ S ∈ M, S.card = 4 := by
    intro S hS
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hS
    have hTcard := ((mem_goldenFlats u T).mp hT).1
    rw [Finset.card_compl, Fintype.card_fin, hTcard]
  obtain ⟨S, hS, havoid⟩ := omitted_four_support_of_image_card_le_eight C hcard M hM hfour
  obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hS
  have hzero : ∀ j, columnZeroSet C j ≠ T := by
    intro j hj
    apply havoid j
    have h := congrArg (fun S : Finset (Fin 8) => Sᶜ) hj
    simpa only [columnZeroSet_eq_compl_columnSupport, compl_compl] using h
  have hselected := omitted_selected_density u σ hσ T hT
    (reconstructionZeroSet (reconstruct E u)) (by
      intro j
      simpa only [hC, reconstructionZeroSet, columnZeroSet] using hzero j)
  have hdense := zero_pattern_rank_density_from_selected_ranks u hu E hE hselected
  have hCm : Matrix.of (reconstruct E u) = C := hC
  change Matrix.of (reconstruct E u) ∈ closure
    {D : Matrix (Fin 8) (Fin n) ℝ | RationalCoordinates D ∧
      D.rank = (Matrix.of (reconstruct E u)).rank ∧
      PreservesZeroEntries (Matrix.of (reconstruct E u)) D} at hdense
  simpa only [hCm] using hdense

/-- In the golden column space, all vectors supported on at most four
specified coordinates form a space of dimension at most one. -/
theorem golden_supported_column_group_rank_le_one {n : ℕ}
    (C : Matrix (Fin 8) (Fin n) ℝ) (hgolden : GoldenIntrinsic C)
    (J : Finset (Fin n)) (O : Finset (Fin 8)) (hO : O.card ≤ 4)
    (hsupport : ∀ j ∈ J, ∀ i, i ∉ O → C i j = 0) :
    subsetRank C.col J ≤ 1 := by
  obtain ⟨u, E, hu, hE, ⟨σ, hσ⟩, hC⟩ := hgolden
  have hgu := golden_of_catalogue u σ hσ
  have hmul : u * E = C := (reconstruct_eq_matrix_mul E u).symm.trans hC
  let F := columnMask E J
  let U := maskRows u Oᶜ
  have hproduct : columnMask C J = u * F := by
    ext i j
    by_cases hj : j ∈ J
    · simpa [F, columnMask, Matrix.mul_apply, hj] using (congrFun (congrFun hmul i) j).symm
    · simp [F, columnMask, Matrix.mul_apply, hj]
  have hzero : U * F = 0 := by
    ext i j
    by_cases hi : i ∈ Oᶜ
    · have hiO : i ∉ O := Finset.mem_compl.mp hi
      by_cases hj : j ∈ J
      · have h := (congrFun (congrFun hmul i) j).trans (hsupport j hj i hiO)
        simpa [U, F, maskRows, columnMask, Matrix.mul_apply, hi, hj] using h
      · simp [U, F, maskRows, columnMask, Matrix.mul_apply, hj]
    · simp [U, maskRows, Matrix.mul_apply, hi]
  have hcomp : 3 ≤ (Oᶜ).card := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨T, hTO, hTcard⟩ := Finset.exists_subset_card_eq hcomp
  have hT := hgu.small_rank T (by omega)
  have hmono := MatroidChecked.GoldenSelectedRanks.subsetRank_mono u hTO
  have hU : 3 ≤ U.rank := by
    have hUeq : U.rank = subsetRank u Oᶜ :=
      maskRows_rank (fun i j => u i j) Oᶜ
    omega
  have hsum := Matrix.rank_add_rank_le_card_of_mul_eq_zero hzero
  simp only [Fintype.card_fin] at hsum
  have hF : F.rank ≤ 1 := by omega
  rw [← columnMask_rank, hproduct]
  exact (Matrix.rank_mul_le_right u F).trans hF

/-- The full golden exceptional branch for two supported column groups.
Their common columns vanish because a nonzero golden column needs at least
four entries whereas the common row support has at most one coordinate. -/
theorem golden_two_group_matrix_density {n : ℕ}
    (C : Matrix (Fin 8) (Fin n) ℝ) (hgolden : GoldenIntrinsic C)
    (hcard : ((activeColumns C).image (columnSupport C)).card ≤ 8)
    (J K : Finset (Fin n)) (O₁ O₂ : Finset (Fin 8))
    (hO₁ : O₁.card ≤ 4) (hO₂ : O₂.card ≤ 4) (hinter : (O₁ ∩ O₂).card ≤ 1)
    (hs₁ : ∀ j ∈ J, ∀ i, i ∉ O₁ → C i j = 0)
    (hs₂ : ∀ j ∈ K, ∀ i, i ∉ O₂ → C i j = 0) :
    C ∈ closure {D : Matrix (Fin 8) (Fin n) ℝ |
      RationalCoordinates D ∧ D.rank = C.rank ∧ PreservesZeroEntries C D ∧
      subsetRank D.col J = subsetRank C.col J ∧
      subsetRank D.col K = subsetRank C.col K} := by
  apply rational_density_two_rank_at_most_one_groups C J K
    (golden_supported_column_group_rank_le_one C hgolden J O₁ hO₁ hs₁)
    (golden_supported_column_group_rank_le_one C hgolden K O₂ hO₂ hs₂)
  · intro j hj i
    by_contra hij
    have hja := (mem_activeColumns C j).mpr ⟨i, hij⟩
    have hmin := hgolden.column_support j hja
    have hsub : columnSupport C j ⊆ O₁ ∩ O₂ := by
      intro a ha
      have hne := (Finset.mem_filter.mp ha).2
      apply Finset.mem_inter.mpr
      constructor
      · by_contra hn
        exact hne (hs₁ j (Finset.mem_inter.mp hj).1 a hn)
      · by_contra hn
        exact hne (hs₂ j (Finset.mem_inter.mp hj).2 a hn)
    have hle := Finset.card_le_card hsub
    omega
  · exact golden_matrix_density_of_few_supports C hgolden hcard

#print axioms golden_two_group_matrix_density

end Papers.RationalityTen.FixedCoordinateFlagDensity

end
end
end BundlePart4

section BundlePart5
/- Original module: Papers.IntrinsicTwoGroupDensity. -/

@[expose] public section
noncomputable section

open Matrix Module Set Filter Topology
open scoped BigOperators

namespace Papers.RationalityTen.FixedCoordinateFlagDensity

open ChirotopeDensity PlaneRationalization
open MatroidChecked.MatrixClassificationCore

/-- Enumerate precisely a finite coordinate support. -/
def supportInjection {s : ℕ} (O : Finset (Fin s)) : Fin (Fintype.card O) → Fin s :=
  fun i => ((Fintype.equivFin O).symm i).val

theorem supportInjection_injective {s : ℕ} (O : Finset (Fin s)) :
    Function.Injective (supportInjection O) :=
  Subtype.val_injective.comp (Fintype.equivFin O).symm.injective

theorem supportInjection_range {s : ℕ} (O : Finset (Fin s)) :
    Set.range (supportInjection O) = (↑O : Set (Fin s)) := by
  ext i
  constructor
  · rintro ⟨j, rfl⟩
    exact ((Fintype.equivFin O).symm j).property
  · intro hi
    refine ⟨Fintype.equivFin O ⟨i, hi⟩, ?_⟩
    simp only [supportInjection, Equiv.symm_apply_apply]

/-- Exact intrinsic chirotope density, transported through a full
annihilator, preserves both small outside-column ranks. -/
theorem two_group_matrix_density_of_intrinsic_density {s r n : ℕ}
    (u : Matrix (Fin s) (Fin r) ℝ) (hu : Spans u)
    (E : Matrix (Fin r) (Fin n) ℝ) (hE : LinearIndependent ℝ E)
    (C : Matrix (Fin s) (Fin n) ℝ) (hC : reconstruct E u = C)
    (hdense : u ∈ closure (RationalRealizations u))
    (J K : Finset (Fin n)) (O₁ O₂ : Finset (Fin s))
    (hO₁ : O₁.card ≤ 4) (hO₂ : O₂.card ≤ 4) (hinter : (O₁ ∩ O₂).card ≤ 1)
    (hs₁ : ∀ j ∈ J, ∀ i, i ∉ O₁ → C i j = 0)
    (hs₂ : ∀ j ∈ K, ∀ i, i ∉ O₂ → C i j = 0) :
    C ∈ closure {D : Matrix (Fin s) (Fin n) ℝ |
      RationalCoordinates D ∧ D.rank = C.rank ∧ PreservesZeroEntries C D ∧
      subsetRank D.col J = subsetRank C.col J ∧
      subsetRank D.col K = subsetRank C.col K} := by
  obtain ⟨m, A, hdim, hA, hAu, _, hAcl⟩ := exists_dense_full_configuration_annihilator u hu hdense
  have hmul : u * E = C := (reconstruct_eq_matrix_mul E u).symm.trans hC
  have hAC : A * C = 0 := by
    rw [← hmul, ← Matrix.mul_assoc, hAu, Matrix.zero_mul]
  have hArank : A.rank = m := by
    simpa only [Fintype.card_fin] using hA.rank_matrix
  have hCrank : C.rank = r := by
    have hCmat : Matrix.of (reconstruct E u) = C := hC
    rw [← hCmat, Matrix.rank_eq_finrank_span_row]
    exact intrinsic_rank_of_reconstruction u hu E hE
  have hfull : A.rank + C.rank = s := by omega
  refine rational_density_two_small_column_groups A C hAC hfull hAcl J K
    (by simpa only [Fintype.card_coe] using hO₁)
    (supportInjection O₁) (supportInjection_injective O₁)
    (by simpa only [Fintype.card_coe] using hO₂)
    (supportInjection O₂) (supportInjection_injective O₂) ?_ ?_ (O₁ ∩ O₂) hinter ?_
  · intro i hi j hj
    have hi' : i ∉ (↑O₁ : Set (Fin s)) := by
      simpa only [supportInjection_range] using hi
    exact hs₁ j hj i hi'
  · intro i hi j hj
    have hi' : i ∉ (↑O₂ : Set (Fin s)) := by
      simpa only [supportInjection_range] using hi
    exact hs₂ j hj i hi'
  · intro j hj i hi
    by_cases hi₁ : i ∈ O₁
    · exact hs₂ j (Finset.mem_inter.mp hj).2 i
        (fun hi₂ => hi (Finset.mem_inter.mpr ⟨hi₁, hi₂⟩))
    · exact hs₁ j (Finset.mem_inter.mp hj).1 i hi₁

#print axioms two_group_matrix_density_of_intrinsic_density

end Papers.RationalityTen.FixedCoordinateFlagDensity

end
end
end BundlePart5

section BundlePart6
/- Original module: Papers.EightRowRelativeMatrixDensity. -/

@[expose] public section
noncomputable section

open Matrix Module Set Filter Topology
open scoped BigOperators

namespace Papers.RationalityTen.FixedCoordinateFlagDensity

open ChirotopeDensity PlaneRationalization
open MatroidChecked.MatrixClassificationCore MatroidChecked.RankFourCatalogueDensity

/-- Complete eight-row matrix assembly with the two selected outside-column
ranks. Nongolden intrinsic configurations use full chirotope density and
relative small-coordinate reconstruction; golden configurations use the
omitted-flat count and rank-one synchronization. The finite rank-four
classification is the sole explicit external theorem input. -/
theorem eight_row_two_group_density_of_positive_kernel
    (hDensity : RankFourDensityInput) {s n : ℕ}
    (C : Matrix (Fin s) (Fin n) ℝ) (hs : s ≤ 8)
    (J K : Finset (Fin n)) (O₁ O₂ : Finset (Fin s))
    (hO₁ : O₁.card ≤ 4) (hO₂ : O₂.card ≤ 4) (hinter : (O₁ ∩ O₂).card ≤ 1)
    (hs₁ : ∀ j ∈ J, ∀ i, i ∉ O₁ → C i j = 0)
    (hs₂ : ∀ j ∈ K, ∀ i, i ∉ O₂ → C i j = 0)
    (hnnz : totalNonzeros C ≤ 36)
    (hoccupied : ∀ i ∈ O₁, ∃ j ∈ J, C i j ≠ 0)
    (hempty : O₁ = ∅ → totalNonzeros C ≤ 32)
    (w : Fin n → ℝ) (hker : C.mulVec w = 0)
    (hpos : ∀ j ∈ J, 0 < w j) (hzero : ∀ j, j ∉ J → w j = 0) :
    C ∈ closure {D : Matrix (Fin s) (Fin n) ℝ |
      RationalCoordinates D ∧ D.rank = C.rank ∧ PreservesZeroEntries C D ∧
      subsetRank D.col J = subsetRank C.col J ∧
      subsetRank D.col K = subsetRank C.col K} := by
  obtain ⟨r, hr, u, E, hu, hE, hC⟩ := exists_intrinsic_linear_configuration C
  have hgo (hcl : u ∈ closure (RationalRealizations u)) :
      C ∈ closure {D : Matrix (Fin s) (Fin n) ℝ |
        RationalCoordinates D ∧ D.rank = C.rank ∧ PreservesZeroEntries C D ∧
        subsetRank D.col J = subsetRank C.col J ∧
        subsetRank D.col K = subsetRank C.col K} :=
    two_group_matrix_density_of_intrinsic_density u hu E hE C hC hcl J K O₁ O₂
      hO₁ hO₂ hinter hs₁ hs₂
  by_cases hs7 : s ≤ 7
  · exact hgo (seven_element_chirotope_density hs7 u hu)
  have hs8 : s = 8 := by omega
  subst s
  by_cases hr4 : r = 4
  · subst r
    by_cases hgolden : HasGoldenMatroid u
    · have hCgolden : GoldenIntrinsic C := ⟨u, E, hu, hE, hgolden, hC⟩
      have hcard := at_most_eight_column_supports_of_positive_kernel C hCgolden.column_support
        hnnz J O₁ hO₁ hs₁ hoccupied hempty w hker hpos hzero
      exact golden_two_group_matrix_density C hCgolden hcard J K O₁ O₂
        hO₁ hO₂ hinter hs₁ hs₂
    · apply hgo
      exact (MatroidChecked.ExactSelectedRanks.exact_density_iff_chirotope_density u).mp
        (hDensity u hu hgolden)
  · exact hgo (eight_element_chirotope_density_of_rank_ne_four (by decide) hr4 u hu)

/-- The two-group statement in the finite-family interface used by the
actual polytope data. Its positive first group may be zero; occupancy and
the empty-support count handle that case without another assumption. -/
theorem eight_row_family_density_of_positive_kernel
    (hDensity : RankFourDensityInput) {s n k : ℕ}
    (C : Matrix (Fin s) (Fin n) ℝ) (hs : s ≤ 8)
    (hkpos : 0 < k) (hk : k ≤ 2)
    (J : Fin k → Finset (Fin n)) (O : Fin k → Finset (Fin s))
    (hO : ∀ a, (O a).card ≤ 4)
    (hinter : ∀ a b, a ≠ b → (O a ∩ O b).card ≤ 1)
    (hsupport : ∀ a j, j ∈ J a → ∀ i, i ∉ O a → C i j = 0)
    (hnnz : totalNonzeros C ≤ 36)
    (hoccupied : ∀ i ∈ O ⟨0, hkpos⟩, ∃ j ∈ J ⟨0, hkpos⟩, C i j ≠ 0)
    (hempty : O ⟨0, hkpos⟩ = ∅ → totalNonzeros C ≤ 32)
    (w : Fin n → ℝ) (hker : C.mulVec w = 0)
    (hpos : ∀ j ∈ J ⟨0, hkpos⟩, 0 < w j)
    (hzero : ∀ j, j ∉ J ⟨0, hkpos⟩ → w j = 0) :
    C ∈ closure {D : Matrix (Fin s) (Fin n) ℝ |
      RationalCoordinates D ∧ D.rank = C.rank ∧ PreservesZeroEntries C D ∧
      ∀ a, subsetRank C.col (J a) = subsetRank D.col (J a)} := by
  have hcases : k = 1 ∨ k = 2 := by omega
  rcases hcases with rfl | rfl
  · have hc := eight_row_two_group_density_of_positive_kernel hDensity C hs
      (J 0) ∅ (O 0) ∅ (hO 0) (by simp) (by simp) (hsupport 0)
      (by intro j hj; exact (Finset.notMem_empty j hj).elim)
      hnnz hoccupied hempty w hker hpos hzero
    apply closure_mono ?_ hc
    intro D hD
    refine ⟨hD.1, hD.2.1, hD.2.2.1, ?_⟩
    intro a
    have ha : a = 0 := Subsingleton.elim _ _
    subst a
    exact hD.2.2.2.1.symm
  · have hc := eight_row_two_group_density_of_positive_kernel hDensity C hs
      (J 0) (J 1) (O 0) (O 1) (hO 0) (hO 1) (hinter 0 1 (by decide))
      (hsupport 0) (hsupport 1) hnnz hoccupied hempty w hker hpos hzero
    apply closure_mono ?_ hc
    intro D hD
    refine ⟨hD.1, hD.2.1, hD.2.2.1, ?_⟩
    intro a
    fin_cases a
    · exact hD.2.2.2.1.symm
    · exact hD.2.2.2.2.symm

#print axioms eight_row_two_group_density_of_positive_kernel

end Papers.RationalityTen.FixedCoordinateFlagDensity

end
end
end BundlePart6

section BundlePart7
/- Original module: Papers.ActualReducedMatrixDensity. -/

@[expose] public section
noncomputable section

open Matrix Module Set Filter Topology
open scoped BigOperators

namespace Papers.RationalityTen.ChirotopeDensity

open FixedCoordinateFlagDensity MatroidChecked.MatrixClassificationCore

/-- Every reduced matrix arising from a positive number of exceptional
facets has the exact density needed by reconstruction. The positive kernel
weights are the values of an actual strict supporting form, rather than an
extra matrix hypothesis. -/
theorem ReducedFacetMatrixData.dense_of_positive_exceptionCount
    (hDensity : RankFourDensityInput) {n : ℕ}
    (p : Fin n → Fin 5 → ℝ) (g : ℤ) (D : ReducedFacetMatrixData p g)
    (hpos : 0 < D.exceptionCount) : D.Dense := by
  let a₀ : Fin D.exceptionCount := ⟨0, hpos⟩
  obtain ⟨a, ha⟩ := (D.masks_facets a₀).2.1
  let w : Fin n → ℝ := (Matrix.of p).mulVec a
  have hw (j : Fin n) : w j = a ⬝ᵥ p j := dotProduct_comm _ _
  have hker : D.matrix.mulVec w = 0 := by
    change D.matrix.mulVec ((Matrix.of p).mulVec a) = 0
    rw [Matrix.mulVec_mulVec, D.annihilates, Matrix.zero_mulVec]
  have hpositive : ∀ j ∈ (D.masks a₀)ᶜ, 0 < w j := by
    intro j hj
    rw [hw j]
    exact ha.2 j (Finset.mem_compl.mp hj)
  have hzero : ∀ j, j ∉ (D.masks a₀)ᶜ → w j = 0 := by
    intro j hj
    rw [hw j]
    exact ha.1 j (by simpa only [Finset.mem_compl, not_not] using hj)
  have hnnz : totalNonzeros D.matrix ≤ 36 := by
    have h := D.nonzero_count
    have hg := D.polygon_excess_ge_four hpos
    have hc := D.rowCount_le
    omega
  refine eight_row_family_density_of_positive_kernel hDensity D.matrix D.rowCount_le
    hpos D.exceptionCount_le (fun a => (D.masks a)ᶜ) D.outsideRows
    D.outsideRows_card D.outsideRows_inter ?_ hnnz ?_
    (D.outsideRows_empty_nonzero_count a₀) w hker hpositive hzero
  · intro b j hj i hi
    exact D.outsideRows_support b j (Finset.mem_compl.mp hj) i hi
  · intro i hi
    obtain ⟨j, hj, hij⟩ := D.outsideRows_occupied a₀ i hi
    exact ⟨j, Finset.mem_compl.mpr hj, hij⟩

#print axioms ReducedFacetMatrixData.dense_of_positive_exceptionCount

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart7

section BundlePart8
/- Original module: Papers.GlobalEightRelationRows. -/

@[expose] public section
noncomputable section

open Set Matrix
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeRelationBudget Papers.PolytopeFacetSurplus

namespace Papers.RationalityTen.ChirotopeDensity

open MatroidChecked.MatrixClassificationCore

/-- The global, existential-realization reading of Proposition 8(iii).
Eight shared relation rows in one actual realization imply rational density
near every realization of its face lattice. Local polygon ranks are allowed
to change; reduced rows and the two exceptional-facet reconstruction account
for those changes. -/
theorem actual_global_eight_sparse_relations_of_rank_four_density
    (hDensity : RankFourDensityInput) {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hc : Fintype.card (SparseSharedRowIndex P e) ≤ 8) : RationallyDense P := by
  have hnine := MatroidChecked.MatrixClassificationCore.nine_column_exceptional_matrix_density hDensity
  have height := MatroidChecked.MatrixClassificationCore.eight_row_density_or_four_column_support hDensity
  intro Q hPQ
  obtain ⟨φ⟩ := hPQ
  have hQ : Q.IsFullDim := (faceOrderIso_polytope_dim φ).trans hP
  let eQ := e.trans (vertexEquivOfFaceOrder φ)
  by_cases hsmall : (nonsimplicialFacets P).card ≤ 9
  · apply actual_at_most_nine_nonsimplicial_facets_of_exceptional_matrix_density hnine Q hQ
    rw [← nonsimplicialFacets_card_of_faceOrder φ]
    exact hsmall
  have hN : 10 ≤ (nonsimplicialFacets P).card := by omega
  by_cases hnone : (rankDroppingFacets P Q e φ).card = 0
  · have hcQ := no_rankDroppingFacets_sparse_row_count_le P Q e φ hc hnone
    exact actual_polytope_eight_sparse_relations_of_classification hnine height Q hQ eQ hcQ
  let D := actualReducedFacetMatrixData P Q hP e φ hc hN
  have hpositive : 0 < D.exceptionCount := by
    change 0 < Fintype.card (rankDroppingFacets P Q e φ)
    rw [Fintype.card_coe]
    omega
  exact rationallyApproximable_of_reducedFacetMatrixData_density Q hQ eQ
    (polygonExcess Q) D
    (ReducedFacetMatrixData.dense_of_positive_exceptionCount hDensity _ _ D hpositive)

/-- The same global theorem in the original shared-relation index.
Sparse circuit generators have exactly the original relation count. -/
theorem actual_global_eight_shared_relations_of_rank_four_density
    (hDensity : RankFourDensityInput) {n : ℕ}
    (P : ConvexPolytope 4) (hP : P.IsFullDim) (e : Fin n ≃ P.vertices)
    (hc : Fintype.card (ActualSharedRowIndex P e) ≤ 8) : RationallyDense P := by
  apply actual_global_eight_sparse_relations_of_rank_four_density hDensity P hP e
  simpa only [sparseSharedRowIndex_card_eq] using hc

#print axioms actual_global_eight_sparse_relations_of_rank_four_density

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart8

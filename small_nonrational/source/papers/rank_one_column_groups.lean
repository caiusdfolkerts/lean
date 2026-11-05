module
public import Papers.RankOneColumnSynchronization

@[expose] public section
noncomputable section

open Matrix Module Set Filter Topology
open scoped BigOperators

namespace Papers.RationalityTen.FixedCoordinateFlagDensity

open ChirotopeDensity PlaneRationalization

/-- A rank-one group admits a representative chosen from its actual nonzero
columns; every other group column is a real scalar multiple of it. -/
theorem rank_one_group_factorization {p n k : ℕ}
    (g : Fin n → Option (Fin k)) (C : Matrix (Fin p) (Fin n) ℝ) (a : Fin k)
    (hgroup : (groupColumnMask g C a).rank = 1) :
    ∃ rep : Fin n, g rep = some a ∧ C.col rep ≠ 0 ∧
      ∀ j, g j = some a → ∃ t : ℝ, ∀ i, C i j = t * C i rep := by
  classical
  let M := groupColumnMask g C a
  have hM : M ≠ 0 := by
    intro h
    have hr : M.rank = 1 := hgroup
    rw [h, Matrix.rank_zero] at hr
    exact Nat.zero_ne_one hr
  obtain ⟨i, j, hij⟩ : ∃ i j, M i j ≠ 0 := by
    by_contra h
    apply hM
    ext i j
    exact not_not.mp (fun hne => h ⟨i, j, hne⟩)
  have hgj : g j = some a := by
    by_contra h
    exact hij (by simp [M, groupColumnMask, h])
  have heq (b : Fin n) (hb : g b = some a) : M.col b = C.col b := by
    ext i
    simp [M, groupColumnMask, Matrix.col_apply, hb]
  have hj : C.col j ≠ 0 := by
    intro h
    apply hij
    have hz := congrFun h i
    simpa [M, groupColumnMask, hgj, Matrix.col_apply] using hz
  let S := Submodule.span ℝ (Set.range M.col)
  have hdim : finrank ℝ S = 1 := by
    have h := Matrix.rank_eq_finrank_span_cols M
    exact h.symm.trans hgroup
  have hjmem : C.col j ∈ S := by
    rw [← heq j hgj]
    exact Submodule.subset_span (Set.mem_range_self j)
  have hspan : S = Submodule.span ℝ ({C.col j} : Set (Fin p → ℝ)) :=
    eq_span_singleton_of_mem_of_finrank_eq_one hdim hjmem hj
  refine ⟨j, hgj, hj, ?_⟩
  intro b hb
  have hbmem : C.col b ∈ S := by
    rw [← heq b hb]
    exact Submodule.subset_span (Set.mem_range_self b)
  rw [hspan] at hbmem
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hbmem
  refine ⟨t, ?_⟩
  intro i
  have h := congrFun ht i
  simpa only [Pi.smul_apply, smul_eq_mul, Matrix.col_apply] using h.symm

/-- Rank-one group density with no chosen representatives or factorizations
among its hypotheses. The groups are the fibres of an ordinary finite label
map, so they are disjoint by construction. -/
theorem rational_density_preserving_rank_one_groups {p n k : ℕ}
    (g : Fin n → Option (Fin k)) (C : Matrix (Fin p) (Fin n) ℝ)
    (hgroups : ∀ a, (groupColumnMask g C a).rank = 1)
    (hdense : C ∈ closure {D : Matrix (Fin p) (Fin n) ℝ |
      RationalCoordinates D ∧ D.rank = C.rank ∧ PreservesZeroEntries C D}) :
    C ∈ closure {D : Matrix (Fin p) (Fin n) ℝ |
      RationalCoordinates D ∧ D.rank = C.rank ∧ PreservesZeroEntries C D ∧
      ∀ a, (groupColumnMask g D a).rank = 1} := by
  classical
  have hex (a : Fin k) := rank_one_group_factorization g C a (hgroups a)
  choose rep hrep hnonzero hfactor using hex
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
  exact rational_density_with_rank_one_column_groups g rep C w hw hgroups hdense

#print axioms rational_density_preserving_rank_one_groups

end Papers.RationalityTen.FixedCoordinateFlagDensity

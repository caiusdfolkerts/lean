module
public import Papers.MatrixSupportCounts
public import Papers.RationalityTenPolygonRelationRanks
public import Papers.RationalityTenSupportBasics

@[expose] public section

/-!
# The two support consequences of the exceptional eight-element matroid

The finite classification must supply the stated subset ranks. These
lemmas prove the required kernel and row-space conclusions from those
ranks, without assuming a particular golden coordinate parameter.


-/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Set Module Matrix
open scoped Classical

theorem kernel_support_lower_bound {n r k : ℕ}
    (p : Fin n → Fin r → ℝ)
    (hind : ∀ S : Finset (Fin n), S.card ≤ k → subsetRank p S = S.card)
    (v : Fin n → ℝ) (hv : v ≠ 0)
    (hker : (Matrix.of p).transpose.mulVec v = 0) :
    k + 1 ≤ (vectorSupport v).card := by
  by_contra hbound
  have hsmall : (vectorSupport v).card ≤ k := by omega
  have hdim := globalRelationSpace_finrank p (vectorSupport v)
  rw [hind _ hsmall] at hdim
  have hbot : globalRelationSpace p (vectorSupport v) = ⊥ :=
    Submodule.finrank_eq_zero.mp (by omega)
  have hmem : v ∈ globalRelationSpace p (vectorSupport v) := by
    apply (mem_globalRelationSpace_iff _ _ _).mpr
    refine ⟨?_, hker⟩
    intro i hi
    by_contra hvi
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvi⟩)
  rw [hbot] at hmem
  exact hv hmem

theorem row_space_support_lower_bound {n r s : ℕ}
    (p : Fin n → Fin r → ℝ)
    (hspan : ∀ S : Finset (Fin n), s ≤ S.card → subsetRank p S = r)
    (a : Fin r → ℝ) (hv : (Matrix.of p).mulVec a ≠ 0) :
    n + 1 ≤ (vectorSupport ((Matrix.of p).mulVec a)).card + s := by
  let v := (Matrix.of p).mulVec a
  let T := Finset.univ \ vectorSupport v
  by_contra hbound
  have hcard : T.card + (vectorSupport v).card = n := by
    simpa only [T, Finset.card_univ, Fintype.card_fin] using
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (vectorSupport v))
  change ¬ n + 1 ≤ (vectorSupport v).card + s at hbound
  have hTlarge : s ≤ T.card := by omega
  have hTrank := hspan T hTlarge
  have hTspan : Submodule.span ℝ (p '' (↑T : Set (Fin n))) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    simpa only [subsetRank, Module.finrank_fin_fun] using hTrank
  have hker : Submodule.span ℝ (p '' (↑T : Set (Fin n))) ≤ (dotLinear a).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    have hi' : i ∉ vectorSupport v := (Finset.mem_sdiff.mp hi).2
    have hzero : v i = 0 := by
      by_contra hvi
      exact hi' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvi⟩)
    change a ⬝ᵥ p i = 0
    rw [dotProduct_comm]
    exact hzero
  rw [hTspan] at hker
  have haa : a ⬝ᵥ a = 0 := hker (Submodule.mem_top : a ∈ (⊤ : Submodule ℝ _))
  have ha : a = 0 := dotProduct_self_eq_zero.mp haa
  exact hv (by simp only [ha, Matrix.mulVec_zero])

theorem exceptional_kernel_support
    (p : Fin 8 → Fin 4 → ℝ)
    (htriple : ∀ S : Finset (Fin 8), S.card ≤ 3 → subsetRank p S = S.card)
    (v : Fin 8 → ℝ) (hv : v ≠ 0)
    (hker : (Matrix.of p).transpose.mulVec v = 0) :
    4 ≤ (vectorSupport v).card :=
  kernel_support_lower_bound p htriple v hv hker

theorem exceptional_row_space_support
    (p : Fin 8 → Fin 4 → ℝ)
    (hfive : ∀ S : Finset (Fin 8), 5 ≤ S.card → subsetRank p S = 4)
    (v : Fin 8 → ℝ) (hv : v ≠ 0)
    (hrow : v ∈ (Matrix.of p).mulVecLin.range) :
    4 ≤ (vectorSupport v).card := by
  obtain ⟨a, rfl⟩ := hrow
  change 4 ≤ (vectorSupport ((Matrix.of p).mulVec a)).card
  have h := row_space_support_lower_bound p hfive a hv
  omega

/-- Each active column of a relation matrix lying in the exceptional
kernel uses at least four row positions. -/
theorem exceptional_relation_columns_support {n : ℕ}
    (p : Fin 8 → Fin 4 → ℝ)
    (htriple : ∀ S : Finset (Fin 8), S.card ≤ 3 → subsetRank p S = S.card)
    (C : Matrix (Fin 8) (Fin n) ℝ)
    (hLC : (Matrix.of p).transpose * C = 0) :
    ∀ j ∈ activeColumns C, 4 ≤ (columnSupport C j).card := by
  intro j hj
  have hnonzero : C.col j ≠ 0 := by
    intro hz
    obtain ⟨i, hne⟩ := (mem_activeColumns C j).mp hj
    exact hne (congrFun hz i)
  have hker : (Matrix.of p).transpose.mulVec (C.col j) = 0 := by
    ext a
    exact congrFun (congrFun hLC a) j
  exact exceptional_kernel_support p htriple (C.col j) hnonzero hker

end Papers.RationalityTen.ChirotopeDensity

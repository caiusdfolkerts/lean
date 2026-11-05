module
public import Papers.RelativeSmallSupportDensity
public import Papers.ColumnGroupGluing

@[expose] public section
noncomputable section

open Matrix Module Set Filter Topology
open scoped BigOperators

namespace Papers.RationalityTen.FixedCoordinateFlagDensity

open ChirotopeDensity PlaneRationalization

/-- A full annihilator with rational coordinate-rank density permits two
small supported column groups to retain their ranks simultaneously. Common
columns may overlap; their common coordinate support is only required to
have at most one element. All parameters and zero patterns are retained. -/
theorem rational_density_two_small_column_groups {m s n p₁ p₂ : ℕ}
    (A : Matrix (Fin m) (Fin s) ℝ) (C : Matrix (Fin s) (Fin n) ℝ)
    (hAC : A * C = 0) (hfull : A.rank + C.rank = s)
    (hA : A ∈ closure {B : Matrix (Fin m) (Fin s) ℝ |
      RationalCoordinates B ∧ SameSubsetRanks A.col B.col})
    (J K : Finset (Fin n))
    (hp₁ : p₁ ≤ 4) (e₁ : Fin p₁ → Fin s) (he₁ : Function.Injective e₁)
    (hp₂ : p₂ ≤ 4) (e₂ : Fin p₂ → Fin s) (he₂ : Function.Injective e₂)
    (hs₁ : ∀ i, i ∉ Set.range e₁ → ∀ j ∈ J, C i j = 0)
    (hs₂ : ∀ i, i ∉ Set.range e₂ → ∀ j ∈ K, C i j = 0)
    (O : Finset (Fin s)) (hO : O.card ≤ 1)
    (hcommon : ∀ j ∈ J ∩ K, ∀ i, i ∉ O → C i j = 0) :
    C ∈ closure {D : Matrix (Fin s) (Fin n) ℝ |
      RationalCoordinates D ∧ D.rank = C.rank ∧ PreservesZeroEntries C D ∧
      subsetRank D.col J = subsetRank C.col J ∧
      subsetRank D.col K = subsetRank C.col K} := by
  classical
  let S : Set (Matrix (Fin m) (Fin s) ℝ) :=
    {B | RationalCoordinates B ∧ SameSubsetRanks A.col B.col}
  let S₀ : Set (Matrix (Fin m) (Fin s) ℝ × Matrix (Fin s) (Fin n) ℝ) := {z |
    z.1 ∈ S ∧ RationalCoordinates z.2 ∧ z.1 * z.2 = 0 ∧
      z.2.rank = C.rank ∧ PreservesZeroEntries C z.2}
  have hS₀ : (A, C) ∈ closure S₀ :=
    relative_full_kernel_density (X := Matrix (Fin m) (Fin s) ℝ)
      (m := m) (p := s) (n := n) (fun B => B) A continuous_id.continuousAt S hA
      (fun _ h => h.1) (fun _ h => h.2) C hAC hfull
  let D := columnMask C J
  let E := columnMask C K
  have hDsupport : ∀ i, i ∉ Set.range e₁ → ∀ j, D i j = 0 := by
    intro i hi j
    by_cases hj : j ∈ J
    · simp only [D, columnMask, if_pos hj, hs₁ i hi j hj]
    · simp only [D, columnMask, if_neg hj]
  have hEsupport : ∀ i, i ∉ Set.range e₂ → ∀ j, E i j = 0 := by
    intro i hi j
    by_cases hj : j ∈ K
    · simp only [E, columnMask, if_pos hj, hs₂ i hi j hj]
    · simp only [E, columnMask, if_neg hj]
  let S₁ : Set ((Matrix (Fin m) (Fin s) ℝ × Matrix (Fin s) (Fin n) ℝ) ×
      Matrix (Fin s) (Fin n) ℝ) := {z |
    z.1 ∈ S₀ ∧ RationalCoordinates z.2 ∧ z.1.1 * z.2 = 0 ∧
      z.2.rank = D.rank ∧ PreservesZeroEntries D z.2}
  have hS₁ : ((A, C), D) ∈ closure S₁ :=
    relative_small_supported_matrix_density
      (X := Matrix (Fin m) (Fin s) ℝ × Matrix (Fin s) (Fin n) ℝ)
      (m := m) (p := p₁) (s := s) (n := n) hp₁ e₁ he₁ (fun z => z.1) (A, C)
      continuous_fst.continuousAt S₀ hS₀ (fun _ h => h.1.1) (fun _ h => h.1.2)
      D (columnMask_mul_zero A C J hAC) hDsupport
  let S₂ : Set (((Matrix (Fin m) (Fin s) ℝ × Matrix (Fin s) (Fin n) ℝ) ×
      Matrix (Fin s) (Fin n) ℝ) × Matrix (Fin s) (Fin n) ℝ) := {z |
    z.1 ∈ S₁ ∧ RationalCoordinates z.2 ∧ z.1.1.1 * z.2 = 0 ∧
      z.2.rank = E.rank ∧ PreservesZeroEntries E z.2}
  have hS₂ : (((A, C), D), E) ∈ closure S₂ :=
    relative_small_supported_matrix_density
      (X := (Matrix (Fin m) (Fin s) ℝ × Matrix (Fin s) (Fin n) ℝ) ×
        Matrix (Fin s) (Fin n) ℝ)
      (m := m) (p := p₂) (s := s) (n := n) hp₂ e₂ he₂ (fun z => z.1.1) ((A, C), D)
      (continuous_fst.comp continuous_fst).continuousAt S₁ hS₁
      (fun _ h => h.1.1.1) (fun _ h => h.1.1.2)
      E (columnMask_mul_zero A C K hAC) hEsupport
  let F : (((Matrix (Fin m) (Fin s) ℝ × Matrix (Fin s) (Fin n) ℝ) ×
      Matrix (Fin s) (Fin n) ℝ) × Matrix (Fin s) (Fin n) ℝ) →
      Matrix (Fin s) (Fin n) ℝ :=
    fun z => mergeColumnGroups z.1.1.2 z.1.2 z.2 J K
  have hF : Continuous F := by
    have hC₀ : Continuous (fun z : (((Matrix (Fin m) (Fin s) ℝ ×
        Matrix (Fin s) (Fin n) ℝ) × Matrix (Fin s) (Fin n) ℝ) ×
        Matrix (Fin s) (Fin n) ℝ) => z.1.1.2) :=
      continuous_snd.comp (continuous_fst.comp continuous_fst)
    have hD₀ : Continuous (fun z : (((Matrix (Fin m) (Fin s) ℝ ×
        Matrix (Fin s) (Fin n) ℝ) × Matrix (Fin s) (Fin n) ℝ) ×
        Matrix (Fin s) (Fin n) ℝ) => z.1.2) :=
      continuous_snd.comp continuous_fst
    exact (replaceColumns_continuous J).comp
      (((replaceColumns_continuous K).comp (hC₀.prodMk continuous_snd)).prodMk hD₀)
  have hbase : F (((A, C), D), E) = C := mergeColumnGroups_self C J K
  have hlow : ∀ᶠ z in 𝓝 (((A, C), D), E), C.rank ≤ (F z).rank := by
    have ht : Tendsto F (𝓝 (((A, C), D), E)) (𝓝 C) := by
      simpa only [hbase] using (hF.continuousAt (x := (((A, C), D), E))).tendsto
    have hRank : ∀ᶠ C' in 𝓝 C, C.rank ≤ C'.rank := by
      let L := Classical.choice (exists_rowKernelChart C)
      filter_upwards [L.eventually_independent] with C' hC'
      have hr : (C'.submatrix L.rows id).rank = L.rank := by
        simpa only [Fintype.card_fin] using
          (LinearIndependent.rank_matrix (M := C'.submatrix L.rows id) hC')
      have hle := Matrix.rank_submatrix_le C' L.rows id
      rw [hr, ← L.rank_eq] at hle
      exact hle
    exact ht.eventually hRank
  have hDn : ∀ᶠ z : (((Matrix (Fin m) (Fin s) ℝ × Matrix (Fin s) (Fin n) ℝ) ×
      Matrix (Fin s) (Fin n) ℝ) × Matrix (Fin s) (Fin n) ℝ)
      in 𝓝 (((A, C), D), E), ∀ i j, D i j ≠ 0 → z.1.2 i j ≠ 0 :=
    ((show Continuous (fun z : (((Matrix (Fin m) (Fin s) ℝ ×
      Matrix (Fin s) (Fin n) ℝ) × Matrix (Fin s) (Fin n) ℝ) ×
      Matrix (Fin s) (Fin n) ℝ) => z.1.2) from
      continuous_snd.comp continuous_fst).continuousAt
        (x := (((A, C), D), E))).tendsto.eventually (eventually_nonzero_entries D)
  have hEn : ∀ᶠ z : (((Matrix (Fin m) (Fin s) ℝ × Matrix (Fin s) (Fin n) ℝ) ×
      Matrix (Fin s) (Fin n) ℝ) × Matrix (Fin s) (Fin n) ℝ)
      in 𝓝 (((A, C), D), E), ∀ i j, E i j ≠ 0 → z.2 i j ≠ 0 :=
    ((show Continuous (fun z : (((Matrix (Fin m) (Fin s) ℝ ×
      Matrix (Fin s) (Fin n) ℝ) × Matrix (Fin s) (Fin n) ℝ) ×
      Matrix (Fin s) (Fin n) ℝ) => z.2) from continuous_snd).continuousAt
        (x := (((A, C), D), E))).tendsto.eventually (eventually_nonzero_entries E)
  have hc := mem_closure_image (hF.continuousAt (x := (((A, C), D), E)))
    (mem_closure_inter_of_eventually hS₂ (hlow.and (hDn.and hEn)))
  rw [hbase] at hc
  apply closure_mono (s := F '' _) ?_ hc
  rintro _ ⟨⟨⟨⟨A', C'⟩, D'⟩, E'⟩, ⟨hz, hl, hnD, hnE⟩, rfl⟩
  rcases hz with ⟨⟨⟨hA', hCrat, hAC', hCrank, hCZ⟩,
    hDrat, hAD', hDrank, hDZ⟩, hErat, hAE', hErank, hEZ⟩
  have hACmerge : A' * mergeColumnGroups C' D' E' J K = 0 := by
    apply replaceColumns_mul_eq_zero A' _ D' J
    · apply replaceColumns_mul_eq_zero A' C' E' K hAC'
      intro j _
      ext i
      exact congrFun (congrFun hAE' i) j
    · intro j _
      ext i
      exact congrFun (congrFun hAD' i) j
  have hArank : A'.rank = A.rank := by
    have h := hA'.2 Finset.univ
    rw [subsetRank_col_univ, subsetRank_col_univ] at h
    exact h.symm
  have hupper := Matrix.rank_add_rank_le_card_of_mul_eq_zero hACmerge
  simp only [Fintype.card_fin] at hupper
  rw [hArank] at hupper
  have hrank : (mergeColumnGroups C' D' E' J K).rank = C.rank := by
    change C.rank ≤ (mergeColumnGroups C' D' E' J K).rank at hl
    omega
  have hDout : ∀ i j, j ∉ J → D' i j = 0 := by
    intro i j hj
    exact hDZ i j (by simp only [D, columnMask, if_neg hj])
  have hEout : ∀ i j, j ∉ K → E' i j = 0 := by
    intro i j hj
    exact hEZ i j (by simp only [E, columnMask, if_neg hj])
  have hcommonD : ∀ j ∈ J ∩ K, ∀ i, i ∉ O → D' i j = 0 := by
    intro j hj i hi
    apply hDZ i j
    simp only [D, columnMask, if_pos (Finset.mem_inter.mp hj).1,
      hcommon j hj i hi]
  have hcommonE : ∀ j ∈ J ∩ K, ∀ i, i ∉ O → E' i j = 0 := by
    intro j hj i hi
    apply hEZ i j
    simp only [E, columnMask, if_pos (Finset.mem_inter.mp hj).2,
      hcommon j hj i hi]
  have hzero : ∀ j ∈ J ∩ K, ∀ i, E' i j = 0 ↔ D' i j = 0 := by
    intro j hj i
    have hjJ := (Finset.mem_inter.mp hj).1
    have hjK := (Finset.mem_inter.mp hj).2
    by_cases hij : C i j = 0
    · have hDz := hDZ i j (by simp only [D, columnMask, if_pos hjJ, hij])
      have hEz := hEZ i j (by simp only [E, columnMask, if_pos hjK, hij])
      exact ⟨fun _ => hDz, fun _ => hEz⟩
    · have hDn' : D' i j ≠ 0 := hnD i j (by simpa only [D, columnMask, if_pos hjJ] using hij)
      have hEn' : E' i j ≠ 0 := hnE i j (by simpa only [E, columnMask, if_pos hjK] using hij)
      exact ⟨fun h => (hEn' h).elim, fun h => (hDn' h).elim⟩
  refine ⟨replaceColumns_rational _ _ J
      (replaceColumns_rational C' E' K hCrat hErat) hDrat, hrank, ?_, ?_, ?_⟩
  · exact replaceColumns_preservesZeroEntries C _ D' J
      (replaceColumns_preservesZeroEntries C C' E' K hCZ
        (columnMask_preservesZeroEntries C E' K hEZ))
      (columnMask_preservesZeroEntries C D' J hDZ)
  · rw [← columnMask_rank, mergeColumnGroups_first C' D' E' J K hDout,
      hDrank, columnMask_rank]
  · rw [← columnMask_rank, mergeColumnGroups_second C' D' E' J K hEout,
      replaceColumns_small_common_support_rank E' D' (J ∩ K) O hO hcommonE hcommonD hzero,
      hErank, columnMask_rank]

#print axioms rational_density_two_small_column_groups

end Papers.RationalityTen.FixedCoordinateFlagDensity

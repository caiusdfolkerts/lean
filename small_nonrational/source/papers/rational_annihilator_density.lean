module
public import Papers.LowCorankGaleDensity

@[expose] public section
noncomputable section
open Matrix Module Set Filter Topology
open scoped BigOperators
namespace Papers.RationalityTen.ChirotopeDensity
open PlaneRationalization

/-- Exact chirotope density transfers to an annihilator while preserving
every coordinate-subset rank. The argument is rank-independent and retains
the actual labelled duality, including both zero and full-rank cases. -/
theorem rational_gale_lift_of_chirotope_density {r n k : ℕ}
    (A : Matrix (Fin r) (Fin n) ℝ) (B : Matrix (Fin n) (Fin k) ℝ)
    (hA : LinearIndependent ℝ A.row) (hB : Spans B)
    (hAB : A*B=0) (hdim : k+r=n)
    (hBcl : B ∈ closure (RationalRealizations B)) :
    A ∈ closure {A' : Matrix (Fin r) (Fin n) ℝ |
      RationalCoordinates A' ∧ SameSubsetRanks A.col A'.col} := by
  have hexact := exact_of_matrix_dimensions A B hA hB hAB hdim
  have hAcl := rationalCoordinates_dense r n A
  have hprod : (B,A) ∈ closure
      (RationalRealizations B ×ˢ {M : Matrix (Fin r) (Fin n) ℝ |
        RationalCoordinates M}) := by
    rw [closure_prod_eq]
    exact ⟨hBcl,hAcl⟩
  let F := fun z : Matrix (Fin n) (Fin k) ℝ × Matrix (Fin r) (Fin n) ℝ =>
    galeChart z.1 z.2
  have hF : ContinuousAt F (B,A) := galeChart_continuousAt hB A
  have hFA : F (B,A)=A := galeChart_self B A hAB
  have hrows : ∀ᶠ z in 𝓝 (B,A), LinearIndependent ℝ (F z).row := by
    have hnear : ∀ᶠ M in 𝓝 (F (B,A)), LinearIndependent ℝ M.row := by
      rw [hFA]
      exact hA.eventually
    exact hF.tendsto.eventually hnear
  have hcl := mem_closure_inter_of_eventually hprod hrows
  have himage : A ∈ closure
      (F '' ((RationalRealizations B ×ˢ
        {M : Matrix (Fin r) (Fin n) ℝ | RationalCoordinates M}) ∩
        {z | LinearIndependent ℝ (F z).row})) := by
    have hi := mem_closure_image hF hcl
    rw [hFA] at hi
    exact hi
  apply closure_mono (s := F '' _) ?_ himage
  rintro _ ⟨⟨B',M⟩,⟨⟨hB',hM⟩,hrows'⟩,rfl⟩
  have hBspan : Spans B' := spans_of_zero_minor_pattern hB hB'.2.zero_iff
  have hexact' := exact_of_matrix_dimensions (galeChart B' M) B'
    hrows' hBspan (galeChart_mul hBspan M) hdim
  exact ⟨galeChart_rational hB'.1 hM,
    matrix_gale_preserves_subset_ranks A (galeChart B' M) B B'
      hB hBspan hexact hexact' (hB'.2.sameSubsetRanks hB)⟩

/-- A full column-rank configuration has an actual full row-rank
annihilator, constructed from the kernel basis of its transpose. -/
theorem exists_full_configuration_annihilator {s r : ℕ}
    (u : Matrix (Fin s) (Fin r) ℝ) (hu : Spans u) :
    ∃ m : ℕ, ∃ A : Matrix (Fin m) (Fin s) ℝ,
      r + m = s ∧ LinearIndependent ℝ A.row ∧ A * u = 0 ∧
      u.mulVecLin.range = A.mulVecLin.ker := by
  have hurank : u.transpose.rank = r :=
    (Matrix.rank_transpose u).trans ((spans_iff_matrix_rank u).mp hu)
  have huLI := rowIndependent_of_rank hurank
  obtain ⟨m, V, hdim, hV, hprod, _⟩ := exists_gale_matrix u.transpose huLI
  let A := V.transpose
  have hArank : A.rank = m :=
    (Matrix.rank_transpose V).trans ((spans_iff_matrix_rank V).mp hV)
  have hA := rowIndependent_of_rank hArank
  have hAu : A * u = 0 := by
    have h := congrArg Matrix.transpose hprod
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using h
  have hd : r + m = s := by omega
  exact ⟨m, A, hd, hA, hAu, exact_of_matrix_dimensions A u hA hu hAu hd⟩

/-- Nongolden full configuration density supplies an annihilator stratum
with all labelled coordinate ranks retained, exactly the external parameter
required by the relative four-coordinate lemma. -/
theorem exists_dense_full_configuration_annihilator {s r : ℕ}
    (u : Matrix (Fin s) (Fin r) ℝ) (hu : Spans u)
    (hcl : u ∈ closure (RationalRealizations u)) :
    ∃ m : ℕ, ∃ A : Matrix (Fin m) (Fin s) ℝ,
      r + m = s ∧ LinearIndependent ℝ A.row ∧ A * u = 0 ∧
      u.mulVecLin.range = A.mulVecLin.ker ∧
      A ∈ closure {A' : Matrix (Fin m) (Fin s) ℝ |
        RationalCoordinates A' ∧ SameSubsetRanks A.col A'.col} := by
  obtain ⟨m, A, hdim, hA, hAu, hexact⟩ := exists_full_configuration_annihilator u hu
  exact ⟨m, A, hdim, hA, hAu, hexact,
    rational_gale_lift_of_chirotope_density A u hA hu hAu hdim hcl⟩

#print axioms rational_gale_lift_of_chirotope_density

end Papers.RationalityTen.ChirotopeDensity

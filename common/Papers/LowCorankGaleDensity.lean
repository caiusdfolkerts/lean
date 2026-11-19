module
public import Papers.GaleConfigurationRanks
public import Papers.GaleKernelBasis
public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Lean.Elab.Tactic.Omega

@[expose] public section

noncomputable section

open Matrix Module Set Filter Topology
open scoped BigOperators

namespace Papers.RationalityTen.ChirotopeDensity

open PlaneRationalization

/-- Rational approximations to a low-rank Gale configuration lift
continuously to primal matrices while preserving every subset rank. -/
theorem rational_gale_lift_dense {r n k : ℕ}
    (hn : n ≤ 8) (hk : k ≤ 3)
    (A : Matrix (Fin r) (Fin n) ℝ) (B : Matrix (Fin n) (Fin k) ℝ)
    (hA : LinearIndependent ℝ A.row) (hB : Spans B)
    (hAB : A*B=0) (hdim : k+r=n) :
    A ∈ closure {A' : Matrix (Fin r) (Fin n) ℝ |
      RationalCoordinates A' ∧ SameSubsetRanks A.col A'.col} := by
  have hexact := exact_of_matrix_dimensions A B hA hB hAB hdim
  have hBcl := rational_chirotope_dense_le_three hn hk B
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

theorem low_corank_subset_rank_density {n r : ℕ}
    (hn : n ≤ 8) (hk : n-r ≤ 3)
    (p : Fin n → Fin r → ℝ) (hp : Spans p) :
    p ∈ closure {q | RationalCoordinates q ∧ SameSubsetRanks p q} := by
  let A : Matrix (Fin r) (Fin n) ℝ := (Matrix.of p).transpose
  have hArank : A.rank=r := by
    change (Matrix.of p).transpose.rank = r
    rw [Matrix.rank_transpose]
    exact (spans_iff_matrix_rank p).mp hp
  have hA := rowIndependent_of_rank hArank
  obtain ⟨k,B,hdim,hB,hAB,hexact⟩ := exists_gale_matrix A hA
  have hk' : k ≤ 3 := by omega
  have hcl := rational_gale_lift_dense hn hk' A B hA hB hAB hdim
  let T : Matrix (Fin r) (Fin n) ℝ → (Fin n → Fin r → ℝ) := fun M i j => M j i
  have hT : Continuous T := continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply i).comp (continuous_apply j)
  have htrans := mem_closure_image hT.continuousAt hcl
  have hbase : T A=p := by ext i j; rfl
  rw [hbase] at htrans
  apply closure_mono (s := T '' _) ?_ htrans
  rintro _ ⟨A',hA',rfl⟩
  exact ⟨rationalCoordinates_transpose hA'.1,hA'.2⟩

theorem SameSubsetRanks.zero_minor_iff {n r : ℕ}
    {p q : Fin n → Fin r → ℝ} (h : SameSubsetRanks p q)
    (b : Fin r → Fin n) : minor p b=0 ↔ minor q b=0 := by
  classical
  have hr := h (Finset.univ.image b)
  have hr' :
      finrank ℝ (Submodule.span ℝ (Set.range (p ∘ b))) =
      finrank ℝ (Submodule.span ℝ (Set.range (q ∘ b))) := by
    have he (v : Fin n → Fin r → ℝ) :
        v '' (↑(Finset.univ.image b) : Set (Fin n)) = Set.range (v ∘ b) := by
      ext x
      simp only [Set.mem_image, Finset.mem_coe, Finset.mem_image, Finset.mem_univ,
        true_and, Set.mem_range, Function.comp_apply]
      constructor
      · rintro ⟨j, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨b i, ⟨i, rfl⟩, rfl⟩
    change finrank ℝ (Submodule.span ℝ (p '' ↑(Finset.univ.image b))) =
      finrank ℝ (Submodule.span ℝ (q '' ↑(Finset.univ.image b))) at hr
    rw [he p, he q] at hr
    exact hr
  apply not_iff_not.mp
  change minor p b ≠ 0 ↔ minor q b ≠ 0
  rw [nonzero_minor_iff_independent,nonzero_minor_iff_independent,
    linearIndependent_iff_card_eq_finrank_span,
    linearIndependent_iff_card_eq_finrank_span]
  simpa only [Set.finrank,hr']

theorem low_corank_chirotope_density {n r : ℕ}
    (hn : n ≤ 8) (hk : n-r ≤ 3)
    (p : Fin n → Fin r → ℝ) (hp : Spans p) :
    p ∈ closure (RationalRealizations p) := by
  apply density_of_zero_minor_density
  apply closure_mono (s := {q | RationalCoordinates q ∧ SameSubsetRanks p q}) ?_
    (low_corank_subset_rank_density hn hk p hp)
  intro q hq
  exact ⟨hq.1,fun b hb => (hq.2.zero_minor_iff b).mp hb⟩

/-- All represented oriented matroids on at most seven elements have
dense rational realizations. The proof explicitly constructs the dual
kernel and transports every labelled subset rank. -/
theorem seven_element_chirotope_density {n r : ℕ}
    (hn : n ≤ 7) (p : Fin n → Fin r → ℝ) (hp : Spans p) :
    p ∈ closure (RationalRealizations p) := by
  by_cases hr : r ≤ 3
  · exact rational_chirotope_dense_le_three (by omega) hr p
  · exact low_corank_chirotope_density (by omega) (by omega) p hp

/-- For eight elements the sole rank not covered by the elementary
rank-three and dual rank-three argument is rank four. -/
theorem eight_element_chirotope_density_of_rank_ne_four {n r : ℕ}
    (hn : n ≤ 8) (hr4 : r ≠ 4)
    (p : Fin n → Fin r → ℝ) (hp : Spans p) :
    p ∈ closure (RationalRealizations p) := by
  by_cases hr : r ≤ 3
  · exact rational_chirotope_dense_le_three hn hr p
  · exact low_corank_chirotope_density hn (by omega) p hp


/-- The seven-element density statement in an arbitrary ambient vector
space, with actual full intrinsic coordinates and injective embeddings. -/
theorem seven_element_rational_density {n d : ℕ}
    (hn : n ≤ 7) (p : Fin n → Fin d → ℝ) :
    p ∈ closure {q | RationalCoordinates q ∧ SameRepresentedType p q} := by
  obtain ⟨r,hr,u,E,hu,hE,hp⟩ := exists_intrinsic_linear_configuration p
  have h := embedded_density_of_intrinsic_density u hu E hE
    (seven_element_chirotope_density hn u hu)
  simpa only [hp] using h

theorem intrinsic_rank_of_reconstruction {n r d : ℕ}
    (u : Fin n → Fin r → ℝ) (hu : Spans u)
    (E : Fin r → Fin d → ℝ) (hE : LinearIndependent ℝ E) :
    finrank ℝ (Submodule.span ℝ (Set.range (reconstruct E u))) = r := by
  have hspan : Submodule.span ℝ (Set.range (reconstruct E u)) =
      (frameMap E).range := by
    change Submodule.span ℝ (Set.range (frameMap E ∘ u)) = _
    rw [Set.range_comp,← Submodule.map_span,hu,Submodule.map_top]
  rw [hspan,LinearMap.finrank_range_of_inj (frameMap_injective hE)]
  simp

theorem eight_element_rational_density_of_rank_ne_four {n d : ℕ}
    (hn : n ≤ 8) (p : Fin n → Fin d → ℝ)
    (hr4 : finrank ℝ (Submodule.span ℝ (Set.range p)) ≠ 4) :
    p ∈ closure {q | RationalCoordinates q ∧ SameRepresentedType p q} := by
  obtain ⟨r,hr,u,E,hu,hE,hp⟩ := exists_intrinsic_linear_configuration p
  have hdim := intrinsic_rank_of_reconstruction u hu E hE
  rw [hp] at hdim
  have h := embedded_density_of_intrinsic_density u hu E hE
    (eight_element_chirotope_density_of_rank_ne_four hn (by omega) u hu)
  simpa only [hp] using h

end Papers.RationalityTen.ChirotopeDensity

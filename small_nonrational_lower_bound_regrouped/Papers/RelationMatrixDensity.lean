module
public import Papers.ConstantRankVectorCharts
public import Papers.LowCorankGaleDensity
public import Mathlib.Tactic.FunProp

@[expose] public section

noncomputable section
set_option maxHeartbeats 1000000

open Matrix Module Set Filter Topology
open scoped BigOperators

namespace Papers.RationalityTen.ChirotopeDensity

open PlaneRationalization

theorem maskRows_rational {c r : ℕ} {p : Fin c → Fin r → ℝ}
    (hp : RationalCoordinates p) (S : Finset (Fin c)) :
    RationalCoordinates (maskRows p S) := by
  classical
  intro i j
  by_cases hi : i∈S
  · simpa [maskRows,hi] using hp i j
  · simpa [maskRows,hi] using RatScalar.zero

def PreservesZeroEntries {c n : ℕ} (C C' : Matrix (Fin c) (Fin n) ℝ) : Prop :=
  ∀ i j, C i j=0 → C' i j=0

/-- The matrix step in Proposition 8. A rationally dense row matroid
allows every coordinate functional to be reconstructed in its prescribed
annihilator, preserving the exact rank and every required zero entry. -/
theorem zero_pattern_rank_density_from_chirotope {c r n : ℕ}
    (u : Fin c → Fin r → ℝ) (hu : Spans u)
    (E : Fin r → Fin n → ℝ) (hE : LinearIndependent ℝ E)
    (huc : u ∈ closure (RationalRealizations u)) :
    reconstruct E u ∈ closure
      {C' : Matrix (Fin c) (Fin n) ℝ |
        RationalCoordinates C' ∧
        C'.rank=(Matrix.of (reconstruct E u)).rank ∧
        PreservesZeroEntries (reconstruct E u) C'} := by
  classical
  let Z : Fin n → Finset (Fin c) :=
    fun j => Finset.univ.filter (fun i => reconstruct E u i j=0)
  let A : Fin n → Matrix (Fin c) (Fin r) ℝ := fun j => maskRows u (Z j)
  let C : (j : Fin n) → RowKernelChart (A j) :=
    fun j => Classical.choice (exists_rowKernelChart (A j))
  let W : Fin n → Fin r → ℝ := fun j a => E a j
  have hW : ∀ j, (A j).mulVec (W j)=0 := by
    intro j
    ext i
    by_cases hi : i∈Z j
    · have hiz : reconstruct E u i j=0 := (Finset.mem_filter.mp hi).2
      simpa [A,maskRows,hi,W,reconstruct,frameMap,Matrix.mulVec,dotProduct,
        Finset.sum_apply,smul_eq_mul] using hiz
    · simp [A,maskRows,hi,Matrix.mulVec,dotProduct]
  let G := fun z : (Fin c → Fin r → ℝ) × (Fin n → Fin r → ℝ) =>
    (fun a j => (C j).eval (maskRows z.1 (Z j)) (z.2 j) a)
  have hGbase : G (u,W)=E := by
    ext a j
    exact congrFun ((C j).self (W j) (hW j)) a
  have hGcont : ContinuousAt G (u,W) := by
    apply continuousAt_pi.mpr
    intro a
    apply continuousAt_pi.mpr
    intro j
    have hparam : Continuous
        (fun z : (Fin c → Fin r → ℝ) × (Fin n → Fin r → ℝ) =>
          (maskRows z.1 (Z j),z.2 j)) :=
      ((maskRows_continuous (Z j)).comp continuous_fst).prodMk
        ((continuous_apply j).comp continuous_snd)
    exact (continuous_apply a).continuousAt.comp
      (((C j).continuousAt (W j)).comp_of_eq (hparam.continuousAt (x := (u, W))) rfl)
  let F := fun z : (Fin c → Fin r → ℝ) × (Fin n → Fin r → ℝ) =>
    reconstruct (G z) z.1
  have hFcont : ContinuousAt F (u,W) :=
    continuous_reconstruct.continuousAt.comp (hGcont.prodMk continuous_fst.continuousAt)
  have hFbase : F (u,W)=reconstruct E u := by simp only [F,hGbase]
  have hLI : ∀ᶠ z in 𝓝 (u,W), LinearIndependent ℝ (G z) := by
    have h : ∀ᶠ E' in 𝓝 (G (u,W)), LinearIndependent ℝ E' := by
      rw [hGbase]
      exact hE.eventually
    exact hGcont.tendsto.eventually h
  have hrows : ∀ᶠ z in 𝓝 (u,W), ∀ j,
      LinearIndependent ℝ (fun a => maskRows z.1 (Z j) ((C j).rows a)) := by
    apply eventually_all.mpr
    intro j
    have hparam : Continuous
        (fun z : (Fin c → Fin r → ℝ) × (Fin n → Fin r → ℝ) =>
          maskRows z.1 (Z j)) := (maskRows_continuous (Z j)).comp continuous_fst
    exact (hparam.continuousAt (x := (u,W))).tendsto.eventually
      (C j).eventually_independent
  have hprod : (u,W) ∈ closure
      (RationalRealizations u ×ˢ {W' : Fin n → Fin r → ℝ | RationalCoordinates W'}) := by
    rw [closure_prod_eq]
    exact ⟨huc,rationalCoordinates_dense n r W⟩
  let Good := fun z : (Fin c → Fin r → ℝ) × (Fin n → Fin r → ℝ) =>
    LinearIndependent ℝ (G z) ∧ ∀ j,
      LinearIndependent ℝ (fun a => maskRows z.1 (Z j) ((C j).rows a))
  have hGood : ∀ᶠ z in 𝓝 (u,W), Good z := hLI.and hrows
  have hcl := mem_closure_inter_of_eventually hprod hGood
  have himage : reconstruct E u ∈ closure
      (F '' ((RationalRealizations u ×ˢ
        {W' : Fin n → Fin r → ℝ | RationalCoordinates W'}) ∩ {z | Good z})) := by
    have hi := mem_closure_image hFcont hcl
    rw [hFbase] at hi
    exact hi
  apply closure_mono (s := F '' _) ?_ himage
  rintro _ ⟨⟨u',W'⟩,⟨⟨hu',hW'⟩,hgood⟩,rfl⟩
  have huSpan : Spans u' := spans_of_zero_minor_pattern hu hu'.2.zero_iff
  have hGRat : RationalCoordinates (G (u',W')) := by
    intro a j
    exact (C j).rational (maskRows_rational hu'.1 (Z j)) (hW' j) a
  refine ⟨reconstruct_rational hGRat hu'.1,?_,?_⟩
  · have hnew := intrinsic_rank_of_reconstruction u' huSpan (G (u',W')) hgood.1
    have hold := intrinsic_rank_of_reconstruction u hu E hE
    change (Matrix.of (reconstruct (G (u',W')) u')).rank =
      (Matrix.of (reconstruct E u)).rank
    rw [Matrix.rank_eq_finrank_span_row, Matrix.rank_eq_finrank_span_row]
    exact hnew.trans hold.symm
  · intro i j hij
    have hi : i∈Z j := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hij⟩
    have hrank : (maskRows u' (Z j)).rank=(A j).rank := by
      dsimp only [A]
      rw [maskRows_rank, maskRows_rank]
      exact (hu'.2.sameSubsetRanks hu (Z j)).symm
    have hzero := (C j).mem (maskRows u' (Z j)) hrank (hgood.2 j) (W' j)
    have hz := congrFun hzero i
    simpa [F,G,reconstruct,frameMap,Matrix.mulVec,dotProduct,maskRows,hi,
      Finset.sum_apply,smul_eq_mul] using hz

theorem rational_matrix_zero_pattern_rank_density_seven {c n : ℕ}
    (hc : c ≤ 7) (C : Matrix (Fin c) (Fin n) ℝ) :
    C ∈ closure {C' : Matrix (Fin c) (Fin n) ℝ |
      RationalCoordinates C' ∧ C'.rank=C.rank ∧ PreservesZeroEntries C C'} := by
  obtain ⟨r,hr,u,E,hu,hE,hC⟩ := exists_intrinsic_linear_configuration C
  have h := zero_pattern_rank_density_from_chirotope u hu E hE
    (seven_element_chirotope_density hc u hu)
  rw [hC] at h
  exact h

theorem rational_matrix_zero_pattern_rank_density_eight_nonfour {c n : ℕ}
    (hc : c ≤ 8) (C : Matrix (Fin c) (Fin n) ℝ) (hr4 : C.rank ≠ 4) :
    C ∈ closure {C' : Matrix (Fin c) (Fin n) ℝ |
      RationalCoordinates C' ∧ C'.rank=C.rank ∧ PreservesZeroEntries C C'} := by
  obtain ⟨r,hr,u,E,hu,hE,hC⟩ := exists_intrinsic_linear_configuration C
  have hdim := intrinsic_rank_of_reconstruction u hu E hE
  rw [hC] at hdim
  change finrank ℝ (Submodule.span ℝ (Set.range C.row)) = r at hdim
  rw [← Matrix.rank_eq_finrank_span_row] at hdim
  have h := zero_pattern_rank_density_from_chirotope u hu E hE
    (eight_element_chirotope_density_of_rank_ne_four hc (by omega) u hu)
  rw [hC] at h
  exact h

end Papers.RationalityTen.ChirotopeDensity

module
public import Consolidated.MatrixNormalization
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases
public import MatroidCatalogue.N8R4
public import MatroidChecked.ChartRealization
public import MatroidChecked.ExactDensity
public import MatroidChecked.GoldenIdentification
public import MatroidChecked.GoldenRationalObstruction
public import MatroidChecked.MinorFormulaSpecialization
public import Papers.ExceptionalSupportBounds
public import Papers.RankFourCertificateNormalization
public import Papers.RationalElimination
public import Papers.RelationMatrixDensity
public import Papers.ResidualPolynomialDensity
public import Papers.SmallRelationMatrixCriteria


section BundlePart0
/- Source: MatroidChecked/RankFourPredicates.lean -/




@[expose] public section
noncomputable section

namespace Papers.RationalityTen.MatroidChecked.RankFourCatalogueDensity
open Matrix Set Topology
open VectorBasisFamilies (vectorBases)
open ChartRealization (FamilyRationallyDense)

def HasGoldenMatroid (p : Matrix (Fin 8) (Fin 4) ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 8),
    (vectorBases p).image (fun S => S.image σ) = MatroidCatalogue.N8R4.family 563

def CatalogueDensityProofs : Prop :=
  ∀ i : Fin 832, i ≠ 563 → FamilyRationallyDense (MatroidCatalogue.N8R4.family i.val)

end Papers.RationalityTen.MatroidChecked.RankFourCatalogueDensity

end
end
end BundlePart0

section BundlePart1
/- Source: MatroidChecked/SelectedRankMatrixDensity.lean -/



@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-!
# Matrix reconstruction from only the selected subset ranks

A column functional is reconstructed in the annihilator of its original
zero-row set. Only the ranks of those finitely many sets, and the full
row span, are needed. The remaining oriented matroid may change. This is
therefore applicable to the golden case with an omitted incidence.
-/

namespace Papers.RationalityTen.ChirotopeDensity

open Matrix Module Set Filter Topology
open PlaneRationalization
open scoped BigOperators Classical

def reconstructionZeroSet {c n : ℕ} (C : Matrix (Fin c) (Fin n) ℝ)
    (j : Fin n) : Finset (Fin c) := Finset.univ.filter fun i => C i j = 0

def SelectedRankRealizations {c r n : ℕ} (u : Fin c → Fin r → ℝ)
    (Z : Fin n → Finset (Fin c)) : Set (Fin c → Fin r → ℝ) :=
  {q | RationalCoordinates q ∧ Spans q ∧ ∀ j, subsetRank q (Z j) = subsetRank u (Z j)}

theorem zero_pattern_rank_density_from_selected_ranks {c r n : ℕ}
    (u : Fin c → Fin r → ℝ) (hu : Spans u)
    (E : Fin r → Fin n → ℝ) (hE : LinearIndependent ℝ E)
    (huc : u ∈ closure (SelectedRankRealizations u
      (reconstructionZeroSet (reconstruct E u)))) :
    reconstruct E u ∈ closure
      {C' : Matrix (Fin c) (Fin n) ℝ |
        RationalCoordinates C' ∧
        C'.rank=(Matrix.of (reconstruct E u)).rank ∧
        PreservesZeroEntries (reconstruct E u) C'} := by
  classical
  let Z : Fin n → Finset (Fin c) :=
    reconstructionZeroSet (reconstruct E u)
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
      (SelectedRankRealizations u Z ×ˢ {W' : Fin n → Fin r → ℝ | RationalCoordinates W'}) := by
    rw [closure_prod_eq]
    exact ⟨huc,rationalCoordinates_dense n r W⟩
  let Good := fun z : (Fin c → Fin r → ℝ) × (Fin n → Fin r → ℝ) =>
    LinearIndependent ℝ (G z) ∧ ∀ j,
      LinearIndependent ℝ (fun a => maskRows z.1 (Z j) ((C j).rows a))
  have hGood : ∀ᶠ z in 𝓝 (u,W), Good z := hLI.and hrows
  have hcl := mem_closure_inter_of_eventually hprod hGood
  have himage : reconstruct E u ∈ closure
      (F '' ((SelectedRankRealizations u Z ×ˢ
        {W' : Fin n → Fin r → ℝ | RationalCoordinates W'}) ∩ {z | Good z})) := by
    have hi := mem_closure_image hFcont hcl
    rw [hFbase] at hi
    exact hi
  apply closure_mono (s := F '' _) ?_ himage
  rintro _ ⟨⟨u',W'⟩,⟨⟨hu',hW'⟩,hgood⟩,rfl⟩
  have huSpan : Spans u' := hu'.2.1
  have hGRat : RationalCoordinates (G (u',W')) := by
    intro a j
    exact (C j).rational (maskRows_rational hu'.1 (Z j)) (hW' j) a
  refine ⟨reconstruct_rational hGRat hu'.1,?_,?_⟩
  · have hnew := intrinsic_rank_of_reconstruction u' huSpan (G (u',W')) hgood.1
    have hold := intrinsic_rank_of_reconstruction u hu E hE
    change (Matrix.of (reconstruct (G (u',W')) u')).rank =
      (Matrix.of (reconstruct E u)).rank
    rw [Matrix.rank_eq_finrank_span_row,Matrix.rank_eq_finrank_span_row]
    exact hnew.trans hold.symm
  · intro i j hij
    have hi : i∈Z j := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hij⟩
    have hrank : (maskRows u' (Z j)).rank=(A j).rank := by
      dsimp only [A]
      rw [maskRows_rank,maskRows_rank]
      exact hu'.2.2 j
    have hzero := (C j).mem (maskRows u' (Z j)) hrank (hgood.2 j) (W' j)
    have hz := congrFun hzero i
    simpa [F,G,reconstruct,frameMap,Matrix.mulVec,dotProduct,maskRows,hi,
      Finset.sum_apply,smul_eq_mul] using hz

end Papers.RationalityTen.ChirotopeDensity

end
end
end BundlePart1

section BundlePart2
/- Source: Papers/SelectedRankNormalizationDensity.lean -/




@[expose] public section

/-!
# Transporting selected ranks out of a normalized chart

The exceptional rank-four chart need only preserve the ranks of the actual
zero-row sets used in matrix reconstruction.  This file transports precisely
those ranks, and the full span, through all real changes of basis and gauges.
The real gauges are approximated jointly with the chart coordinates; their
invertibility is retained by an open condition.
-/

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Matrix Set Filter Topology
open scoped BigOperators

namespace Papers.MatrixGaugeNormalization

open Papers.RationalityTen.ChirotopeDensity
open Papers.RationalityTen.PlaneRationalization

theorem maskRows_mul_right {n r : ℕ} (p : Matrix (Fin n) (Fin r) ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (S : Finset (Fin n)) :
    maskRows (p * A) S = maskRows p S * A := by
  classical
  ext i j
  by_cases hi : i ∈ S <;> simp [maskRows, hi, Matrix.mul_apply]

theorem subsetRank_mul_right {n r : ℕ} (p : Matrix (Fin n) (Fin r) ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (hA : A.det ≠ 0) (S : Finset (Fin n)) :
    subsetRank (p * A) S = subsetRank p S := by
  calc
    subsetRank (p * A) S = (maskRows (p * A) S).rank := (maskRows_rank _ _).symm
    _ = (maskRows p S * A).rank := congrArg Matrix.rank (maskRows_mul_right p A S)
    _ = (maskRows p S).rank := Matrix.rank_mul_eq_left_of_det_ne_zero A _ hA
    _ = subsetRank p S := maskRows_rank _ _

theorem spans_mul_right {n r : ℕ} (p : Matrix (Fin n) (Fin r) ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (hA : A.det ≠ 0) (hp : Spans p) :
    Spans (p * A) := by
  apply (spans_iff_matrix_rank _).mpr
  change (p * A).rank = r
  rw [Matrix.rank_mul_eq_left_of_det_ne_zero A p hA]
  exact (spans_iff_matrix_rank p).mp hp

theorem scaleRowsColumns_eq_diagonal_mul {n r : ℕ}
    (p : Matrix (Fin n) (Fin r) ℝ) (a : Fin n → ℝ) (b : Fin r → ℝ) :
    scaleRowsColumns p a b = Matrix.diagonal a * p * Matrix.diagonal b := by
  ext i j
  simp only [scaleRowsColumns, Matrix.of_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem scaleRowsColumns_rank {n r : ℕ}
    (p : Matrix (Fin n) (Fin r) ℝ) (a : Fin n → ℝ) (b : Fin r → ℝ)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ j, b j ≠ 0) :
    (scaleRowsColumns p a b).rank = p.rank := by
  have hda : (Matrix.diagonal a).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => ha i
  have hdb : (Matrix.diagonal b).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hb i
  rw [scaleRowsColumns_eq_diagonal_mul,
    Matrix.rank_mul_eq_left_of_det_ne_zero _ _ hdb,
    Matrix.rank_mul_eq_right_of_det_ne_zero _ _ hda]

theorem maskRows_scaleRowsColumns {n r : ℕ}
    (p : Matrix (Fin n) (Fin r) ℝ) (a : Fin n → ℝ) (b : Fin r → ℝ)
    (S : Finset (Fin n)) :
    maskRows (scaleRowsColumns p a b) S = scaleRowsColumns (maskRows p S) a b := by
  classical
  ext i j
  by_cases hi : i ∈ S <;> simp [maskRows, scaleRowsColumns, hi]

theorem subsetRank_scaleRowsColumns {n r : ℕ}
    (p : Matrix (Fin n) (Fin r) ℝ) (a : Fin n → ℝ) (b : Fin r → ℝ)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ j, b j ≠ 0) (S : Finset (Fin n)) :
    subsetRank (scaleRowsColumns p a b) S = subsetRank p S := by
  calc
    subsetRank (scaleRowsColumns p a b) S =
        (maskRows (scaleRowsColumns p a b) S).rank := (maskRows_rank _ _).symm
    _ = (scaleRowsColumns (maskRows p S) a b).rank :=
      congrArg Matrix.rank (maskRows_scaleRowsColumns p a b S)
    _ = (maskRows p S).rank := scaleRowsColumns_rank _ _ _ ha hb
    _ = subsetRank p S := maskRows_rank _ _

theorem spans_scaleRowsColumns {n r : ℕ}
    (p : Matrix (Fin n) (Fin r) ℝ) (a : Fin n → ℝ) (b : Fin r → ℝ)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ j, b j ≠ 0) (hp : Spans p) :
    Spans (scaleRowsColumns p a b) := by
  apply (spans_iff_matrix_rank _).mpr
  change (scaleRowsColumns p a b).rank = r
  rw [scaleRowsColumns_rank _ _ _ ha hb]
  exact (spans_iff_matrix_rank p).mp hp

theorem subsetRank_permuted_rows {n r : ℕ}
    (p : Matrix (Fin n) (Fin r) ℝ) (e : Equiv.Perm (Fin n))
    (S : Finset (Fin n)) :
    subsetRank (p.submatrix e id) (S.image e.symm) = subsetRank p S := by
  classical
  have heq : (p.submatrix e id) '' (↑(S.image e.symm) : Set (Fin n)) =
      p '' (↑S : Set (Fin n)) := by
    ext y
    constructor
    · rintro ⟨i, hi, rfl⟩
      change i ∈ S.image e.symm at hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      exact ⟨j, hj, by ext k; simp⟩
    · rintro ⟨i, hi, rfl⟩
      refine ⟨e.symm i, Finset.mem_image.mpr ⟨i, hi, rfl⟩, ?_⟩
      ext k
      simp
  unfold subsetRank
  rw [heq]

theorem spans_permuted_rows {n r : ℕ}
    (p : Matrix (Fin n) (Fin r) ℝ) (e : Equiv.Perm (Fin n)) (hp : Spans p) :
    Spans (p.submatrix e id) := by
  have heq : Set.range (p.submatrix e id) = Set.range p := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e.symm i, by ext k; simp⟩
  change Submodule.span ℝ (Set.range (p.submatrix e id)) = ⊤
  rw [heq]
  exact hp

theorem right_mul_selected_density {n r m : ℕ}
    (p : Matrix (Fin n) (Fin r) ℝ) (Z : Fin m → Finset (Fin n))
    (A : Matrix (Fin r) (Fin r) ℝ) (hA : A.det ≠ 0)
    (hp : p ∈ closure (SelectedRankRealizations p Z)) :
    p * A ∈ closure (SelectedRankRealizations (p * A) Z) := by
  have hAc : A ∈ closure {B : Matrix (Fin r) (Fin r) ℝ |
      RationalCoordinates B ∧ B.det ≠ 0} := by
    have hd : ∀ᶠ B in 𝓝 A, B.det ≠ 0 :=
      (continuous_id.matrix_det.continuousAt).eventually_ne hA
    have h := mem_closure_inter_of_eventually (rational_matrices_dense r r A) hd
    change A ∈ closure ({B | Papers.RationalKernelCharts.RationalCoordinates B} ∩
      {B : Matrix (Fin r) (Fin r) ℝ | B.det ≠ 0})
    exact h
  have hprod : (p, A) ∈ closure (SelectedRankRealizations p Z ×ˢ
      {B : Matrix (Fin r) (Fin r) ℝ | RationalCoordinates B ∧ B.det ≠ 0}) := by
    rw [closure_prod_eq]
    exact ⟨hp, hAc⟩
  let f : Matrix (Fin n) (Fin r) ℝ × Matrix (Fin r) (Fin r) ℝ →
      Matrix (Fin n) (Fin r) ℝ := fun z => z.1 * z.2
  have hf : Continuous f := continuous_fst.matrix_mul continuous_snd
  have hcl := mem_closure_image hf.continuousAt hprod
  apply closure_mono (s := f '' _) ?_ hcl
  rintro _ ⟨⟨q, B⟩, ⟨hq, hB⟩, rfl⟩
  refine ⟨Papers.RationalKernelCharts.rationalCoordinates_mul hq.1 hB.1,
    spans_mul_right q B hB.2 hq.2.1, ?_⟩
  intro j
  rw [subsetRank_mul_right q B hB.2, subsetRank_mul_right p A hA]
  exact hq.2.2 j

theorem nonzero_rational_scalars_closure {n : ℕ} (a : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) :
    a ∈ closure {b : Fin n → ℝ |
      (∀ i, Papers.RationalKernelCharts.RatScalar (b i)) ∧ ∀ i, b i ≠ 0} := by
  have hn : ∀ᶠ b in 𝓝 a, ∀ i, b i ≠ 0 := by
    apply eventually_all.mpr
    intro i
    exact (continuous_apply i).continuousAt.eventually_ne (ha i)
  have h := mem_closure_inter_of_eventually (rational_scalars_dense n a) hn
  change a ∈ closure ({b | ∀ i, Papers.RationalKernelCharts.RatScalar (b i)} ∩
    {b : Fin n → ℝ | ∀ i, b i ≠ 0})
  exact h

theorem scale_selected_density {n r m : ℕ}
    (p : Matrix (Fin n) (Fin r) ℝ) (Z : Fin m → Finset (Fin n))
    (a : Fin n → ℝ) (b : Fin r → ℝ)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ j, b j ≠ 0)
    (hp : p ∈ closure (SelectedRankRealizations p Z)) :
    scaleRowsColumns p a b ∈ closure (SelectedRankRealizations
      (scaleRowsColumns p a b) Z) := by
  have hprod : (p, a, b) ∈ closure (SelectedRankRealizations p Z ×ˢ
      ({c : Fin n → ℝ | (∀ i, Papers.RationalKernelCharts.RatScalar (c i)) ∧
        ∀ i, c i ≠ 0} ×ˢ
       {d : Fin r → ℝ | (∀ j, Papers.RationalKernelCharts.RatScalar (d j)) ∧
        ∀ j, d j ≠ 0})) := by
    rw [closure_prod_eq, closure_prod_eq]
    exact ⟨hp, nonzero_rational_scalars_closure a ha,
      nonzero_rational_scalars_closure b hb⟩
  let f : Matrix (Fin n) (Fin r) ℝ × (Fin n → ℝ) × (Fin r → ℝ) →
      Matrix (Fin n) (Fin r) ℝ := fun z => scaleRowsColumns z.1 z.2.1 z.2.2
  have hcl := mem_closure_image (continuous_scaleRowsColumns n r).continuousAt hprod
  apply closure_mono (s := f '' _) ?_ hcl
  rintro _ ⟨⟨q, c, d⟩, ⟨hq, hc, hd⟩, rfl⟩
  refine ⟨scaleRowsColumns_rational q c d hq.1 hc.1 hd.1,
    spans_scaleRowsColumns q c d hc.2 hd.2 hq.2.1, ?_⟩
  intro j
  rw [subsetRank_scaleRowsColumns q c d hc.2 hd.2,
    subsetRank_scaleRowsColumns p a b ha hb]
  exact hq.2.2 j

theorem permuted_rows_selected_density {n r m : ℕ}
    (p : Matrix (Fin n) (Fin r) ℝ) (Z : Fin m → Finset (Fin n))
    (e : Equiv.Perm (Fin n)) (hp : p ∈ closure (SelectedRankRealizations p Z)) :
    p.submatrix e id ∈ closure (SelectedRankRealizations (p.submatrix e id)
      (fun j => (Z j).image e.symm)) := by
  let f : Matrix (Fin n) (Fin r) ℝ → Matrix (Fin n) (Fin r) ℝ :=
    fun q => q.submatrix e id
  have hf : Continuous f := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact continuous_apply_apply (e i) j
  have hcl := mem_closure_image hf.continuousAt hp
  apply closure_mono (s := f '' _) ?_ hcl
  rintro _ ⟨q, hq, rfl⟩
  refine ⟨fun i j => hq.1 (e i) j, spans_permuted_rows q e hq.2.1, ?_⟩
  intro j
  rw [subsetRank_permuted_rows, subsetRank_permuted_rows]
  exact hq.2.2 j

theorem selected_density_of_permuted_rows {n r m : ℕ}
    (p : Matrix (Fin n) (Fin r) ℝ) (Z : Fin m → Finset (Fin n))
    (e : Equiv.Perm (Fin n))
    (hp : p.submatrix e id ∈ closure (SelectedRankRealizations (p.submatrix e id)
      (fun j => (Z j).image e.symm))) :
    p ∈ closure (SelectedRankRealizations p Z) := by
  classical
  have h := permuted_rows_selected_density (p.submatrix e id)
    (fun j => (Z j).image e.symm) e.symm hp
  have heq : (p.submatrix e id).submatrix e.symm id = p := by
    ext i j
    simp [Matrix.submatrix]
  have hZ : (fun j => ((Z j).image e.symm).image e.symm.symm) = Z := by
    funext j
    ext i
    simp
  simpa only [heq, hZ] using h

theorem selected_density_of_normalized_chart {n r m : ℕ}
    (p : Matrix (Fin n) (Fin r) ℝ) (Z : Fin m → Finset (Fin n))
    (b : Fin r → Fin n) (hb : (basisMatrix p b).det ≠ 0)
    (a : Fin n → ℝ) (c : Fin r → ℝ) (ha : ∀ i, a i ≠ 0) (hc : ∀ j, c j ≠ 0)
    (hchart : scaleRowsColumns (normalizeBasis p b) a c ∈ closure
      (SelectedRankRealizations (scaleRowsColumns (normalizeBasis p b) a c) Z)) :
    p ∈ closure (SelectedRankRealizations p Z) := by
  have hundo := scale_selected_density (scaleRowsColumns (normalizeBasis p b) a c) Z
    (fun i => (a i)⁻¹) (fun j => (c j)⁻¹)
    (fun i => inv_ne_zero (ha i)) (fun j => inv_ne_zero (hc j)) hchart
  rw [scaleRowsColumns_inverse _ a c ha hc] at hundo
  have hfinal := right_mul_selected_density (normalizeBasis p b) Z (basisMatrix p b) hb hundo
  simpa only [normalizeBasis_reconstruct p b hb] using hfinal

/-- Exact transport of a selected set of original labels into the chart. -/
theorem ScheduledRankFourChart.selected_subsetRank
    {p : Matrix (Fin 8) (Fin 4) ℝ} {e : Equiv.Perm (Fin 8)}
    {edges : List (Fin 8 × Fin 8)} (D : ScheduledRankFourChart p e edges)
    (S : Finset (Fin 8)) :
    subsetRank D.matrix (S.image e.symm) = subsetRank p S := by
  rw [ScheduledRankFourChart.matrix, normalizedMatrix,
    subsetRank_scaleRowsColumns _ _ _ D.rowScale_nonzero D.columnScale_nonzero]
  unfold normalizeBasis
  have hdet : ((basisMatrix (p.submatrix e id) firstFour)⁻¹).det ≠ 0 := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
    exact inv_ne_zero D.basis_nonsingular
  rw [subsetRank_mul_right _ _ hdet, subsetRank_permuted_rows]

/-- Preserving only the specified subset ranks in the normalized chart is
enough to preserve exactly those ranks in the original representation. -/
theorem ScheduledRankFourChart.selected_density {m : ℕ}
    {p : Matrix (Fin 8) (Fin 4) ℝ} {e : Equiv.Perm (Fin 8)}
    {edges : List (Fin 8 × Fin 8)} (D : ScheduledRankFourChart p e edges)
    (Z : Fin m → Finset (Fin 8))
    (h : D.matrix ∈ closure (SelectedRankRealizations D.matrix
      (fun j => (Z j).image e.symm))) :
    p ∈ closure (SelectedRankRealizations p Z) := by
  apply selected_density_of_permuted_rows p Z e
  exact selected_density_of_normalized_chart _ _ _ D.basis_nonsingular _ _
    D.rowScale_nonzero D.columnScale_nonzero h

end Papers.MatrixGaugeNormalization

end
end
end BundlePart2

section BundlePart3
/- Source: MatroidChecked/ExactSelectedRanks.lean -/




@[expose] public section
noncomputable section

namespace Papers.RationalityTen.MatroidChecked.ExactSelectedRanks

open Matrix Module Set Filter Topology
open ChirotopeDensity ExactDensity

/-- The full maximal-minor zero pattern determines all subset ranks once
the configuration spans. This applies also to repeated and zero rows. -/
theorem exactRealizations_selected {c r n : ℕ}
    (p : Matrix (Fin c) (Fin r) ℝ) (hp : Spans p)
    (Z : Fin n → Finset (Fin c)) :
    ExactRationalRealizations p ⊆ SelectedRankRealizations p Z := by
  intro q hq
  have hzero : ∀ b, minor p b = 0 ↔ minor q b = 0 := hq.2
  have hqspan : Spans q := spans_of_zero_minor_pattern hp hzero
  refine ⟨hq.1,hqspan,?_⟩
  intro j
  apply Nat.le_antisymm
  · exact finrank_span_image_le_of_independence_imp q p
      (fun T hT => independent_of_zero_minor_pattern hqspan
        (fun b => (hzero b).symm) hT) (Z j)
  · exact finrank_span_image_le_of_independence_imp p q
      (fun T hT => independent_of_zero_minor_pattern hp hzero hT) (Z j)

theorem selected_density_of_exact_density {c r n : ℕ}
    (p : Matrix (Fin c) (Fin r) ℝ) (hp : Spans p)
    (Z : Fin n → Finset (Fin c))
    (hdense : p ∈ closure (ExactRationalRealizations p)) :
    p ∈ closure (SelectedRankRealizations p Z) :=
  closure_mono (exactRealizations_selected p hp Z) hdense

/-- Exact zero-pattern density and oriented-matroid density are equivalent.
The reverse implication retains signs in a sufficiently small open neighborhood;
there is no loss of mathematical strength in using zero minors during elimination. -/
theorem exact_density_iff_chirotope_density {n r : ℕ}
    (p : Matrix (Fin n) (Fin r) ℝ) :
    p ∈ closure (ExactRationalRealizations p) ↔
      p ∈ closure (ChirotopeDensity.RationalRealizations p) := by
  constructor
  · intro hp
    apply ChirotopeDensity.density_of_zero_minor_density p
    apply closure_mono (s := ExactRationalRealizations p) ?_ hp
    rintro q ⟨hRat,hzero⟩
    refine ⟨hRat,?_⟩
    intro b hb
    exact (hzero b).mp hb
  · intro hp
    apply closure_mono (s := ChirotopeDensity.RationalRealizations p) ?_ hp
    rintro q ⟨hRat,hchi⟩
    exact ⟨hRat,hchi.zero_iff⟩

end Papers.RationalityTen.MatroidChecked.ExactSelectedRanks

end
end
end BundlePart3

section BundlePart4
/- Source: MatroidChecked/GoldenSelectedRanks.lean -/






@[expose] public section
noncomputable section

/-!
# The golden omission argument preserves precisely the needed ranks

For the exceptional rank-four matroid every set of at most three rows is
independent, and every set of at least five rows spans. Consequently its
only non-open rank requirements are the nine dependent four-sets. If one
of those sets never occurs as a column zero set, rational approximation
preserving the other eight incidences preserves all ranks needed by the
column-kernel reconstruction. Full golden chirotope density is not used.
-/

namespace Papers.RationalityTen.MatroidChecked.GoldenSelectedRanks

open Matrix Module Set Filter Topology Finset
open ChirotopeDensity
open ChartPolynomial ChartRealization GoldenIdentification
open VectorBasisFamilies (vectorBases mem_vectorBases span_image_eq_range
  det_zero_iff_not_basis_image)
open scoped Classical

def Golden (p : Matrix Point Coordinate ℝ) : Prop :=
  ∃ σ : Equiv.Perm Point,
    (vectorBases p).image (fun S => S.image σ) = goldenFamily

theorem golden_of_catalogue (p : Matrix Point Coordinate ℝ)
    (σ : Equiv.Perm Point)
    (hσ : (vectorBases p).image (fun S => S.image σ) =
      MatroidCatalogue.N8R4.family 563) : Golden p := by
  refine ⟨σ.trans catalogueToPaper,?_⟩
  have h := congrArg (fun F : Finset (Finset Point) =>
    F.image (fun S => S.image catalogueToPaper)) hσ
  simpa only [goldenFamily,Finset.image_image,Equiv.coe_trans,Function.comp_def,Equiv.trans_apply] using h

theorem basis_relabel_iff (p : Matrix Point Coordinate ℝ)
    (σ : Equiv.Perm Point)
    (hσ : (vectorBases p).image (fun S => S.image σ) = goldenFamily)
    (S : Finset Point) : S ∈ vectorBases p ↔ S.image σ ∈ goldenFamily := by
  rw [← hσ]
  constructor
  · exact Finset.mem_image_of_mem _
  · intro h
    obtain ⟨T,hT,hTS⟩ := Finset.mem_image.mp h
    have heq := Finset.image_injective σ.injective hTS
    exact heq ▸ hT

theorem subsetRank_le_card (p : Matrix Point Coordinate ℝ) (S : Finset Point) :
    subsetRank p S ≤ S.card := by
  have h : finrank ℝ (Submodule.span ℝ (Set.range fun i : S => p i.val)) ≤ S.card := by
    simpa only [Set.finrank,Fintype.card_coe] using
      finrank_range_le_card (R:=ℝ) (fun i : S => p i.val)
  have heq := congrArg (fun T : Set (Coordinate → ℝ) =>
    finrank ℝ (Submodule.span ℝ T)) (span_image_eq_range (fun i => p i) S)
  exact heq.le.trans h

theorem subsetRank_le_four (p : Matrix Point Coordinate ℝ) (S : Finset Point) :
    subsetRank p S ≤ 4 := by
  have h := Submodule.finrank_mono
    (show Submodule.span ℝ (p '' (S : Set Point)) ≤ ⊤ from le_top)
  simpa only [subsetRank,finrank_top,Module.finrank_fin_fun] using h

theorem subsetRank_mono (p : Matrix Point Coordinate ℝ)
    {S T : Finset Point} (h : S ⊆ T) : subsetRank p S ≤ subsetRank p T :=
  Submodule.finrank_mono (Submodule.span_mono (Set.image_mono h))

theorem subsetRank_eq_card_iff (p : Matrix Point Coordinate ℝ) (S : Finset Point) :
    subsetRank p S = S.card ↔ LinearIndepOn ℝ p (S : Set Point) := by
  have h : LinearIndependent ℝ (fun i : S => p i.val) ↔
      Fintype.card S = (Set.range (fun i : S => p i.val)).finrank ℝ :=
    linearIndependent_iff_card_eq_finrank_span
  have heq : subsetRank p S =
      finrank ℝ (Submodule.span ℝ (Set.range fun i : S => p i.val)) :=
    congrArg (fun T : Set (Coordinate → ℝ) => finrank ℝ (Submodule.span ℝ T))
      (span_image_eq_range (fun i => p i) S)
  constructor
  · intro hs
    exact h.mpr (by simpa only [Fintype.card_coe,Set.finrank] using hs.symm.trans heq)
  · intro hi
    exact heq.trans (by simpa only [Fintype.card_coe,Set.finrank] using (h.mp hi).symm)

theorem subsetRank_four_iff_basis (p : Matrix Point Coordinate ℝ)
    (S : Finset Point) (hS : S.card = 4) :
    subsetRank p S = 4 ↔ S ∈ vectorBases p := by
  constructor
  · intro h
    exact (mem_vectorBases p S).mpr
      ⟨hS,(subsetRank_eq_card_iff p S).mp (h.trans hS.symm)⟩
  · intro h
    exact ((subsetRank_eq_card_iff p S).mpr ((mem_vectorBases p S).mp h).2).trans hS

theorem Golden.small_independent {p : Matrix Point Coordinate ℝ} (hp : Golden p)
    (S : Finset Point) (hS : S.card ≤ 3) : LinearIndepOn ℝ p (S : Set Point) := by
  obtain ⟨σ,hσ⟩ := hp
  obtain ⟨T,hST,_,hT⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ S) hS (by decide : 3 ≤ (Finset.univ : Finset Point).card)
  have hTimage : (T.image σ).card = 3 := by
    rw [Finset.card_image_of_injective _ σ.injective,hT]
  obtain ⟨A,hA,hTA⟩ := golden_triples_extend (T.image σ) hTimage
  let B := A.image σ.symm
  have hBimage : B.image σ = A := by
    simp only [B,Finset.image_image,Function.comp_def,Equiv.apply_symm_apply,Finset.image_id,Finset.image_id']
  have hB : B ∈ vectorBases p := (basis_relabel_iff p σ hσ B).mpr (hBimage.symm ▸ hA)
  have hSB : S ⊆ B := by
    intro i hi
    exact Finset.mem_image.mpr ⟨σ i,hTA (Finset.mem_image_of_mem σ (hST hi)),
      σ.symm_apply_apply i⟩
  exact ((mem_vectorBases p B).mp hB).2.mono hSB

theorem Golden.small_rank {p : Matrix Point Coordinate ℝ} (hp : Golden p)
    (S : Finset Point) (hS : S.card ≤ 3) : subsetRank p S = S.card :=
  (subsetRank_eq_card_iff p S).mpr (hp.small_independent S hS)

theorem Golden.large_rank {p : Matrix Point Coordinate ℝ} (hp : Golden p)
    (S : Finset Point) (hS : 5 ≤ S.card) : subsetRank p S = 4 := by
  obtain ⟨σ,hσ⟩ := hp
  obtain ⟨T,hTS,hT⟩ := Finset.exists_subset_card_eq hS
  have hTimage : (T.image σ).card = 5 := by
    rw [Finset.card_image_of_injective _ σ.injective,hT]
  obtain ⟨A,hA,hAT⟩ := golden_fives_contain_basis (T.image σ) hTimage
  let B := A.image σ.symm
  have hBimage : B.image σ = A := by
    simp only [B,Finset.image_image,Function.comp_def,Equiv.apply_symm_apply,Finset.image_id,Finset.image_id']
  have hB : B ∈ vectorBases p := (basis_relabel_iff p σ hσ B).mpr (hBimage.symm ▸ hA)
  have hBS : B ⊆ S := by
    intro i hi
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨j,hj,hja⟩ := Finset.mem_image.mp (hAT ha)
    have hja' : σ.symm a = j := by rw [← hja,σ.symm_apply_apply]
    exact hja'.symm ▸ hTS hj
  have hBrank : subsetRank p B = 4 :=
    (subsetRank_four_iff_basis p B ((mem_vectorBases p B).mp hB).1).mpr hB
  have hlo := subsetRank_mono p hBS
  have hup := subsetRank_le_four p S
  omega

theorem Golden.spans {p : Matrix Point Coordinate ℝ} (hp : Golden p) : Spans p := by
  have h := hp.large_rank Finset.univ (by decide)
  have heq : p '' (↑(Finset.univ : Finset Point) : Set Point) = Set.range p := by
    ext y
    constructor
    · rintro ⟨i,_,hi⟩
      exact ⟨i,hi⟩
    · rintro ⟨i,hi⟩
      exact ⟨i,Finset.mem_univ _,hi⟩
  apply Submodule.eq_top_of_finrank_eq
  simpa only [Module.finrank_fin_fun] using
    (congrArg (fun T : Set (Coordinate → ℝ) =>
      finrank ℝ (Submodule.span ℝ T)) heq).symm.trans h

def goldenFlats (p : Matrix Point Coordinate ℝ) : Finset (Finset Point) :=
  (Finset.univ : Finset Point).powersetCard 4 \ vectorBases p

@[simp] theorem mem_goldenFlats (p : Matrix Point Coordinate ℝ) (S : Finset Point) :
    S ∈ goldenFlats p ↔ S.card = 4 ∧ S ∉ vectorBases p := by
  simp [goldenFlats]

theorem paperNonbases_card : paperNonbases.card = 9 := by decide +kernel

theorem Golden.flats_card {p : Matrix Point Coordinate ℝ} (hp : Golden p) :
    (goldenFlats p).card = 9 := by
  obtain ⟨σ,hσ⟩ := hp
  have himage : (goldenFlats p).image (fun S => S.image σ) = paperNonbases := by
    rw [← golden_nonbases_exact]
    ext A
    constructor
    · intro h
      obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp h
      obtain ⟨hcard,hnot⟩ := (mem_goldenFlats p S).mp hS
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,?_⟩,?_⟩
      · rwa [Finset.card_image_of_injective _ σ.injective]
      · exact fun h => hnot ((basis_relabel_iff p σ hσ S).mpr h)
    · intro h
      obtain ⟨hcard,hnot⟩ := Finset.mem_sdiff.mp h
      have hcA := (Finset.mem_powersetCard.mp hcard).2
      let S := A.image σ.symm
      have heq : S.image σ = A := by
        simp only [S,Finset.image_image,Function.comp_def,Equiv.apply_symm_apply,Finset.image_id,Finset.image_id']
      apply Finset.mem_image.mpr
      refine ⟨S,(mem_goldenFlats p S).mpr ⟨?_,?_⟩,heq⟩
      · simpa only [S,Finset.card_image_of_injective _ σ.symm.injective] using hcA
      · intro hS
        exact hnot (heq ▸ (basis_relabel_iff p σ hσ S).mp hS)
  have hcard := congrArg Finset.card himage
  rw [Finset.card_image_of_injective _ (Finset.image_injective σ.injective),
    paperNonbases_card] at hcard
  exact hcard

def PartialZeroRealizations (p : Matrix Point Coordinate ℝ) (omitted : Finset Point) :
    Set (Matrix Point Coordinate ℝ) :=
  {q | ChirotopeDensity.RationalCoordinates q ∧ ∀ S : Finset Point,
    S.card = 4 → S ≠ omitted → S ∉ vectorBases p → S ∉ vectorBases q}

theorem eventually_subset_rank_ge (p : Matrix Point Coordinate ℝ) (S : Finset Point) :
    ∀ᶠ q : Matrix Point Coordinate ℝ in 𝓝 p, subsetRank p S ≤ subsetRank q S := by
  let C := Classical.choice (exists_rowKernelChart (maskRows p S))
  have he := (maskRows_continuous S).continuousAt.tendsto.eventually C.eventually_independent
  filter_upwards [he] with q hq
  have hr : ((maskRows q S).submatrix C.rows id).rank = C.rank := by
    have hh := LinearIndependent.rank_matrix
      (M := (maskRows q S).submatrix C.rows id) hq
    simpa only [Fintype.card_fin] using hh
  have hle := Matrix.rank_submatrix_le (maskRows q S) C.rows id
  calc
    subsetRank p S = (maskRows p S).rank := (maskRows_rank _ _).symm
    _ = C.rank := C.rank_eq
    _ = ((maskRows q S).submatrix C.rows id).rank := hr.symm
    _ ≤ (maskRows q S).rank := hle
    _ = subsetRank q S := maskRows_rank _ _

/-- The omitted set is excluded only from the application's list of zero
sets. Other ranks may change; every selected rank is proved equal. -/
theorem selected_rank_density_of_partial_zeros
    (p : Matrix Point Coordinate ℝ) (hp : Golden p) (omitted : Finset Point)
    (hdense : p ∈ closure (PartialZeroRealizations p omitted))
    {n : ℕ} (Z : Fin n → Finset Point) (homitted : ∀ j, Z j ≠ omitted) :
    p ∈ closure (SelectedRankRealizations p Z) := by
  have hlow : ∀ᶠ q : Matrix Point Coordinate ℝ in 𝓝 p,
      ∀ S : Finset Point, subsetRank p S ≤ subsetRank q S :=
    eventually_all.mpr (eventually_subset_rank_ge p)
  have hcl := PlaneRationalization.mem_closure_inter_of_eventually hdense hlow
  apply closure_mono (s := PartialZeroRealizations p omitted ∩
    {q | ∀ S : Finset Point, subsetRank p S ≤ subsetRank q S}) ?_ hcl
  rintro q ⟨⟨hRat,hzero⟩,hle⟩
  have hspan : Spans q := by
    have hpU := subsetRank_univ p hp.spans
    have hU := hle Finset.univ
    have hmax := subsetRank_le_four q Finset.univ
    have hqU : subsetRank q Finset.univ = 4 := by omega
    have heq : q '' (↑(Finset.univ : Finset Point) : Set Point) = Set.range q := by
      ext y
      constructor
      · rintro ⟨i,_,hi⟩
        exact ⟨i,hi⟩
      · rintro ⟨i,hi⟩
        exact ⟨i,Finset.mem_univ _,hi⟩
    apply Submodule.eq_top_of_finrank_eq
    simpa only [Module.finrank_fin_fun] using
      (congrArg (fun T : Set (Coordinate → ℝ) =>
        finrank ℝ (Submodule.span ℝ T)) heq).symm.trans hqU
  refine ⟨hRat,hspan,?_⟩
  intro j
  let S := Z j
  change subsetRank q S = subsetRank p S
  have hlo := hle S
  by_cases hsmall : S.card ≤ 3
  · have hpS := hp.small_rank S hsmall
    have hqS := subsetRank_le_card q S
    omega
  by_cases hlarge : 5 ≤ S.card
  · have hpS := hp.large_rank S hlarge
    have hqS := subsetRank_le_four q S
    omega
  have hfour : S.card = 4 := by omega
  by_cases hb : S ∈ vectorBases p
  · have hpS := (subsetRank_four_iff_basis p S hfour).mpr hb
    have hqS := subsetRank_le_four q S
    omega
  have hqb := hzero S hfour (homitted j) hb
  have hpNe : subsetRank p S ≠ 4 := fun h => hb ((subsetRank_four_iff_basis p S hfour).mp h)
  have hqNe : subsetRank q S ≠ 4 := fun h => hqb ((subsetRank_four_iff_basis q S hfour).mp h)
  obtain ⟨T,hTS,hT⟩ := Finset.exists_subset_card_eq (show 3 ≤ S.card by omega)
  have hpT := hp.small_rank T (by omega)
  have hTSrank := subsetRank_mono p hTS
  have hpmax := subsetRank_le_four p S
  have hqmax := subsetRank_le_four q S
  omega

theorem ChartCertificate.partial_zero_density {ι : Type*} {m u : ℕ}
    {family : Finset (Finset Point)} (C : ChartCertificate ι m u family)
    (hdense : RationalElimination.RationallyDenseSystem C.equations C.units)
    (p : Matrix Point Coordinate ℝ) (σ : Equiv.Perm Point)
    (hcatalogue : (vectorBases p).image (fun S => S.image σ) = family)
    (R : RealizedChart C p σ) (omitted : Finset Point)
    (hrequired : ∀ i, C.basisMark i ≠ true → minorSet i ≠ omitted → C.requiredZero i = true) :
    R.normalized.matrix ∈ closure (PartialZeroRealizations R.normalized.matrix omitted) := by
  have hcl := C.prescribed_density hdense R.point R.solution
  rw [R.matrix_eq] at hcl
  apply closure_mono ?_ hcl
  intro q hq
  refine ⟨hq.1,?_⟩
  intro S hS hne hnonbasis
  obtain ⟨i,rfl⟩ := exists_minorSet S hS
  have hz := (det_zero_iff_not_basis_image R.normalized.matrix (minorRows i)).mpr hnonbasis
  have hmark := (C.scheduled_zero_iff p σ hcatalogue R.normalized i).mp hz
  have hqzero := hq.2 i (hrequired i hmark hne)
  exact (det_zero_iff_not_basis_image q (minorRows i)).mp hqzero

theorem normalized_subset_rank {p : Matrix Point Coordinate ℝ}
    {e : Equiv.Perm Point} {edges : List (Point × Point)}
    (N : Papers.MatrixGaugeNormalization.ScheduledRankFourChart p e edges)
    (S : Finset Point) : subsetRank N.matrix S = subsetRank p (S.image e) := by
  have h := N.selected_subsetRank (S.image e)
  simpa only [Finset.image_image,Function.comp_def,Equiv.symm_apply_apply,
    Finset.image_id,Finset.image_id'] using h

theorem normalized_basis_iff {p : Matrix Point Coordinate ℝ}
    {e : Equiv.Perm Point} {edges : List (Point × Point)}
    (N : Papers.MatrixGaugeNormalization.ScheduledRankFourChart p e edges)
    (S : Finset Point) : S ∈ vectorBases N.matrix ↔ S.image e ∈ vectorBases p := by
  by_cases hc : S.card = 4
  · have hce : (S.image e).card = 4 := by
      rwa [Finset.card_image_of_injective _ e.injective]
    rw [← subsetRank_four_iff_basis N.matrix S hc,
      ← subsetRank_four_iff_basis p (S.image e) hce,normalized_subset_rank N]
  · have hce : (S.image e).card ≠ 4 := by
      rwa [Finset.card_image_of_injective _ e.injective]
    constructor
    · intro h
      exact False.elim (hc ((mem_vectorBases N.matrix S).mp h).1)
    · intro h
      exact False.elim (hce ((mem_vectorBases p (S.image e)).mp h).1)

theorem normalized_basis_image {p : Matrix Point Coordinate ℝ}
    {e : Equiv.Perm Point} {edges : List (Point × Point)}
    (N : Papers.MatrixGaugeNormalization.ScheduledRankFourChart p e edges) :
    (vectorBases N.matrix).image (fun S => S.image e) = vectorBases p := by
  ext S
  constructor
  · rintro h
    obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp h
    exact (normalized_basis_iff N T).mp hT
  · intro hS
    have heq : (S.image e.symm).image e = S := by
      simp only [Finset.image_image,Function.comp_def,Equiv.apply_symm_apply,
        Finset.image_id,Finset.image_id']
    exact Finset.mem_image.mpr ⟨S.image e.symm,
      (normalized_basis_iff N _).mpr (heq.symm ▸ hS),heq⟩

theorem Golden.normalized {p : Matrix Point Coordinate ℝ}
    (hp : Golden p) {e : Equiv.Perm Point} {edges : List (Point × Point)}
    (N : Papers.MatrixGaugeNormalization.ScheduledRankFourChart p e edges) :
    Golden N.matrix := by
  obtain ⟨σ,hσ⟩ := hp
  refine ⟨e.trans σ,?_⟩
  have h := congrArg (fun F : Finset (Finset Point) =>
    F.image (fun S => S.image σ)) (normalized_basis_image N)
  simpa only [Finset.image_image,Equiv.coe_trans,Function.comp_def,Equiv.trans_apply,hσ] using h

/-- The omitted incidence is specified in the catalogue labels. Both the
chosen basis permutation and the original representation's permutation
are transported explicitly through the normalized coordinates. -/
theorem ChartCertificate.selected_density_of_omission {ι : Type*} {m u n : ℕ}
    {family : Finset (Finset Point)} (C : ChartCertificate ι m u family)
    (hdense : RationalElimination.RationallyDenseSystem C.equations C.units)
    (p : Matrix Point Coordinate ℝ) (hp : Golden p) (σ : Equiv.Perm Point)
    (hcatalogue : (vectorBases p).image (fun S => S.image σ) = family)
    (omitted : Finset Point)
    (hrequired : ∀ i, C.basisMark i ≠ true → minorSet i ≠ omitted →
      C.requiredZero i = true)
    (Z : Fin n → Finset Point)
    (havoid : ∀ j, (Z j).image σ ≠ omitted.image
      (BasisCertificates.checkedPermutation 8 C.labelCode C.pattern.permutation_valid)) :
    p ∈ closure (SelectedRankRealizations p Z) := by
  obtain ⟨R⟩ := C.realize p σ hcatalogue
  apply R.normalized.selected_density Z
  apply selected_rank_density_of_partial_zeros R.normalized.matrix
    (hp.normalized R.normalized) omitted
    (ChartCertificate.partial_zero_density C hdense p σ hcatalogue R omitted hrequired)
  intro j heq
  apply havoid j
  have himage := congrArg (fun S : Finset Point => S.image
    (BasisCertificates.checkedPermutation 8 C.labelCode C.pattern.permutation_valid)) heq
  simpa only [ChartCertificate.label,Equiv.symm_trans_apply,Equiv.symm_symm,
    Finset.image_image,Equiv.coe_trans,Function.comp_def,Equiv.trans_apply,
    Equiv.apply_symm_apply] using himage

end Papers.RationalityTen.MatroidChecked.GoldenSelectedRanks

end
end
end BundlePart4

section BundlePart5
/- Source: MatroidChecked/GoldenExceptionExact.lean -/






@[expose] public section
noncomputable section

/-!
# The precise exceptional case in Lemma11

The exception is inhabited by the displayed real matrix and excludes every
rational realization of its represented oriented matroid. The generic
zero-pattern formulation is explicitly linked to determinant signs.
-/

namespace Papers.RationalityTen.MatroidChecked.GoldenExceptionExact
open Matrix Set Topology ChartPolynomial GoldenIdentification
open VectorBasisFamilies (vectorBases mem_vectorBases det_ne_zero_iff_basis_image)
open ChirotopeDensity RankFourCatalogueDensity

lemma orderedMinor_ne_zero_iff_basis (p : Matrix Point Coordinate ℝ)
    (b : Coordinate → Point) :
    (p.submatrix b id).det ≠ 0 ↔ Finset.univ.image b ∈ vectorBases p := by
  have hm : p.submatrix b id = (fun i j => p (b i) j) := by ext i j; rfl
  rw [hm]
  exact det_ne_zero_iff_basis_image p b

theorem vectorBases_eq_of_zero_iff (p q : Matrix Point Coordinate ℝ)
    (hzero : ∀ b : Coordinate → Point,
      (p.submatrix b id).det = 0 ↔ (q.submatrix b id).det = 0) :
    vectorBases p = vectorBases q := by
  ext S
  by_cases hcard : S.card = 4
  · obtain ⟨i,rfl⟩ := exists_minorSet S hcard
    exact (orderedMinor_ne_zero_iff_basis p (minorRows i)).symm.trans
      ((not_congr (hzero (minorRows i))).trans
        (orderedMinor_ne_zero_iff_basis q (minorRows i)))
  · constructor
    · intro h
      exact False.elim (hcard ((mem_vectorBases p S).mp h).1)
    · intro h
      exact False.elim (hcard ((mem_vectorBases q S).mp h).1)

/-- An exceptional real configuration has no rational point of the same
labelled oriented-matroid realization space. -/
theorem golden_realizations_empty (p : Matrix Point Coordinate ℝ)
    (hp : HasGoldenMatroid p) : RationalRealizations p = ∅ := by
  exact Set.eq_empty_iff_forall_notMem.mpr (fun (q : Matrix Point Coordinate ℝ) hq => by
    obtain ⟨hRat,hchi⟩ := hq
    obtain ⟨σ,hσ⟩ := hp
    have hzero : ∀ b, (p.submatrix b id).det = 0 ↔ (q.submatrix b id).det = 0 :=
      hchi.zero_iff
    have hbases := vectorBases_eq_of_zero_iff p q hzero
    have hqcat : (vectorBases q).image (fun S => S.image σ) =
        MatroidCatalogue.N8R4.family 563 :=
      (congrArg (fun F : Finset (Finset Point) => F.image (fun S => S.image σ))
        hbases).symm.trans hσ
    exact GoldenRationalObstruction.no_rational_representation q hRat σ hqcat)

theorem golden_not_rationally_dense (p : Matrix Point Coordinate ℝ)
    (hp : HasGoldenMatroid p) : p ∉ closure (RationalRealizations p) := by
  rw [golden_realizations_empty p hp,closure_empty]
  exact Set.notMem_empty p

/-- The exception is an actual real rank-four configuration, not an empty
formal predicate. Both roots remain covered by the universal identification. -/
theorem exists_spanning_golden :
    ∃ p : Matrix Point Coordinate ℝ, Spans p ∧ HasGoldenMatroid p := by
  let t : ℝ := (Real.sqrt 5 - 1) / 2
  have ht : t^2 + t - 1 = 0 := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
    dsimp only [t]
    nlinarith
  let p := goldenRows t
  have hg : GoldenSelectedRanks.Golden p := by
    refine ⟨Equiv.refl Point,?_⟩
    simpa only [p,Equiv.coe_refl,Finset.image_id,Finset.image_id'] using golden_vectorBases t ht
  refine ⟨p,hg.spans,?_⟩
  apply (golden_isomorphism_iff p t ht).mpr
  exact ⟨Equiv.refl Point,by simp only [p,Equiv.coe_refl,Finset.image_id,Finset.image_id']⟩

end Papers.RationalityTen.MatroidChecked.GoldenExceptionExact

end
end
end BundlePart5

section BundlePart6
/- Source: Consolidated/GoldenOmittedCharts.lean -/










@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/- Source: Charts/Case563Omit0.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart563Omit0
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Option (Fin 0))))))) ℚ :=
  ![X (none) * X (some (some (some (some (some (none)))))) - (X (some (none))), -(X (some (some (none))) * X (some (some (some (some (some (none))))))) + (X (some (some (some (none))))), -(X (none)) + (1), X (some (some (none))) * X (some (some (some (some (none))))) - (X (some (some (none)))) - (X (some (some (some (none))))) + (1), -(X (some (none)) * X (some (some (none)))) + (X (some (none))) - (1)]
noncomputable def U0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Option (Fin 0))))))) ℚ :=
  ![X (some (some (none))), X (none), X (some (none)), X (some (some (some (none)))), X (some (some (some (some (some (none))))))]
noncomputable def R0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Option (Fin 0))))))) ℚ :=
  ![X (none) * X (some (some (some (some (some (none)))))) - (X (some (none))), X (some (some (none))) * X (some (some (some (some (some (none)))))) - (X (some (some (some (none))))), X (none) - (1), X (some (some (none))) * X (some (some (some (some (none))))) - (X (some (some (none)))) - (X (some (some (some (none))))) + (1), X (some (none)) * X (some (some (none))) - (X (some (none))) + (1)]

noncomputable def reductions0 (j : Fin 5) : FactorReduction U0 (E0 j) (R0 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring

noncomputable def nextE0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![-(X (none)) + (X (some (some (some (some (none)))))), X (some (none)) * X (some (some (some (some (none))))) - (X (some (some (none)))), 0, X (some (none)) * X (some (some (some (none)))) - (X (some (none))) - (X (some (some (none)))) + (1), X (none) * X (some (none)) - (X (none)) + (1)]
noncomputable def nextU0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![X (some (none)), 1, X (none), X (some (some (none))), X (some (some (some (some (none)))))]

noncomputable def step0 : LinearStep (Option (Option (Option (Option (Option (Fin 0)))))) 5 5 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := 1
  b := -(1)
  pivot := 2
  pivot_identity := by simp [R0]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 0, 1, 0, 0]
  equation_quotient := ![X (some (some (some (some (some (none)))))), 0, 1, 0, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![0, 1, 0, 0, 0]
  unit_quotient := ![0, 1, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![-(X (none)) + (X (some (some (some (some (none)))))), X (some (none)) * X (some (some (some (some (none))))) - (X (some (some (none)))), 0, X (some (none)) * X (some (some (some (none)))) - (X (some (none))) - (X (some (some (none)))) + (1), X (none) * X (some (none)) - (X (none)) + (1)]
noncomputable def U1 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![X (some (none)), 1, X (none), X (some (some (none))), X (some (some (some (some (none)))))]
noncomputable def R1 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![X (none) - (X (some (some (some (some (none)))))), X (some (none)) * X (some (some (some (some (none))))) - (X (some (some (none)))), 0, X (some (none)) * X (some (some (some (none)))) - (X (some (none))) - (X (some (some (none)))) + (1), X (none) * X (some (none)) - (X (none)) + (1)]

noncomputable def reductions1 (j : Fin 5) : FactorReduction U1 (E1 j) (R1 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring

noncomputable def nextE1 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![0, X (none) * X (some (some (some (none)))) - (X (some (none))), 0, X (none) * X (some (some (none))) - (X (none)) - (X (some (none))) + (1), X (none) * X (some (some (some (none)))) - (X (some (some (some (none))))) + (1)]
noncomputable def nextU1 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (none), 1, X (some (some (some (none)))), X (some (none)), X (some (some (some (none))))]

noncomputable def step1 : LinearStep (Option (Option (Option (Option (Fin 0))))) 5 5 where
  sourceE := R1
  sourceU := U1
  targetE := nextE1
  targetU := nextU1
  a := 1
  b := -(X (some (some (some (none)))))
  pivot := 0
  pivot_identity := by simp [R1]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 0, 0, 0, 1]
  equation_quotient := ![1, 0, 0, 0, X (some (none)) - (1)]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring
  unit_power := ![0, 0, 1, 0, 0]
  unit_quotient := ![0, 0, 1, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring

noncomputable def E2 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![0, X (none) * X (some (some (some (none)))) - (X (some (none))), 0, X (none) * X (some (some (none))) - (X (none)) - (X (some (none))) + (1), X (none) * X (some (some (some (none)))) - (X (some (some (some (none))))) + (1)]
noncomputable def U2 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (none), 1, X (some (some (some (none)))), X (some (none)), X (some (some (some (none))))]
noncomputable def R2 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![0, X (none) * X (some (some (some (none)))) - (X (some (none))), 0, X (none) * X (some (some (none))) - (X (none)) - (X (some (none))) + (1), X (none) * X (some (some (some (none)))) - (X (some (some (some (none))))) + (1)]

noncomputable def reductions2 (j : Fin 5) : FactorReduction U2 (E2 j) (R2 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring

noncomputable def nextE2 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![0, 0, 0, X (none) * X (some (none)) - (X (none) * X (some (some (none)))) - (X (none)) + (X (some (some (none)))), X (none) * X (some (some (none))) - ((X (some (some (none)))) ^ 2) + (X (some (some (none))))]
noncomputable def nextU2 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none), 1, X (some (some (none))), X (none), X (some (some (none)))]

noncomputable def step2 : LinearStep (Option (Option (Option (Fin 0)))) 5 5 where
  sourceE := R2
  sourceU := U2
  targetE := nextE2
  targetU := nextU2
  a := X (some (some (none)))
  b := -(X (none))
  pivot := 1
  pivot_identity := by simp [R2]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 1
      selected := ![2]
      quotient := 1
      identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 1, 0, 1, 1]
  equation_quotient := ![0, X (some (some (some (none)))), 0, X (some (some (none))) - (1), X (some (some (some (none))))]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring
  unit_power := ![1, 0, 0, 0, 0]
  unit_quotient := ![1, 0, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring

noncomputable def E3 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![0, 0, 0, X (none) * X (some (none)) - (X (none) * X (some (some (none)))) - (X (none)) + (X (some (some (none)))), X (none) * X (some (some (none))) - ((X (some (some (none)))) ^ 2) + (X (some (some (none))))]
noncomputable def U3 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none), 1, X (some (some (none))), X (none), X (some (some (none)))]
noncomputable def R3 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![0, 0, 0, -(X (none) * X (some (none))) + (X (none) * X (some (some (none)))) + (X (none)) - (X (some (some (none)))), X (none) - (X (some (some (none)))) + (1)]

noncomputable def reductions3 (j : Fin 5) : FactorReduction U3 (E3 j) (R3 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := X (some (some (none)))
      unit_witness := {
        count := 1
        selected := ![2]
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := X (some (some (none)))
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring

noncomputable def nextE3 : Fin 5 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, 0, 0, -(X (none) * X (some (none))) + (X (none)) + ((X (some (none))) ^ 2) - (X (some (none))) - (1), 0]
noncomputable def nextU3 : Fin 5 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (some (none)) - (1), 1, X (some (none)), X (some (none)) - (1), X (some (none))]

noncomputable def step3 : LinearStep (Option (Option (Fin 0))) 5 5 where
  sourceE := R3
  sourceU := U3
  targetE := nextE3
  targetU := nextU3
  a := 1
  b := -(X (some (none))) + (1)
  pivot := 4
  pivot_identity := by simp [R3]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 0, 0, 1, 1]
  equation_quotient := ![0, 0, 0, -(X (some (none))) + (X (some (some (none)))) + (1), 1]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R3, U3, nextE3, nextU3, map_ofNat] <;> ring
  unit_power := ![1, 0, 0, 1, 0]
  unit_quotient := ![1, 0, 0, 1, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R3, U3, nextE3, nextU3, map_ofNat] <;> ring

noncomputable def E4 : Fin 5 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, 0, 0, -(X (none) * X (some (none))) + (X (none)) + ((X (some (none))) ^ 2) - (X (some (none))) - (1), 0]
noncomputable def U4 : Fin 5 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (some (none)) - (1), 1, X (some (none)), X (some (none)) - (1), X (some (none))]
noncomputable def R4 : Fin 5 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, 0, 0, -(X (none) * X (some (none))) + (X (none)) + ((X (some (none))) ^ 2) - (X (some (none))) - (1), 0]

noncomputable def reductions4 (j : Fin 5) : FactorReduction U4 (E4 j) (R4 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring

noncomputable def nextE4 : Fin 5 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0, 0]
noncomputable def nextU4 : Fin 5 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none) - (1), 1, X (none), X (none) - (1), X (none)]

noncomputable def step4 : LinearStep (Option (Fin 0)) 5 5 where
  sourceE := R4
  sourceU := U4
  targetE := nextE4
  targetU := nextU4
  a := -(X (none)) + (1)
  b := (X (none)) ^ 2 - (X (none)) - (1)
  pivot := 3
  pivot_identity := by simp [R4]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 1
      selected := ![0]
      quotient := -(1)
      identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 0, 0, 1, 0]
  equation_quotient := ![0, 0, 0, -(X (some (none))) + (1), 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R4, U4, nextE4, nextU4, map_ofNat] <;> ring
  unit_power := ![0, 0, 0, 0, 0]
  unit_quotient := ![0, 0, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R4, U4, nextE4, nextU4, map_ofNat] <;> ring

noncomputable def E5 : Fin 5 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0, 0]
noncomputable def U5 : Fin 5 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none) - (1), 1, X (none), X (none) - (1), X (none)]
noncomputable def R5 : Fin 5 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0, 0]

noncomputable def reductions5 (j : Fin 5) : FactorReduction U5 (E5 j) (R5 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U5, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E5, R5]<;> ring
    · simp [E5, R5]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U5, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E5, R5]<;> ring
    · simp [E5, R5]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U5, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E5, R5]<;> ring
    · simp [E5, R5]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U5, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E5, R5]<;> ring
    · simp [E5, R5]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U5, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E5, R5]<;> ring
    · simp [E5, R5]<;> ring

theorem dense5 : RationallyDenseSystem E5 U5 := by
  apply dense_system_of_factor_reductions E5 R5 U5 reductions5
  apply zero_equations_system_dense R5 U5
  intro j; fin_cases j <;> rfl

theorem dense4 : RationallyDenseSystem E4 U4 := by
  apply dense_system_of_factor_reductions E4 R4 U4 reductions4
  exact step4.preserves_density dense5

theorem dense3 : RationallyDenseSystem E3 U3 := by
  apply dense_system_of_factor_reductions E3 R3 U3 reductions3
  exact step3.preserves_density dense4

theorem dense2 : RationallyDenseSystem E2 U2 := by
  apply dense_system_of_factor_reductions E2 R2 U2 reductions2
  exact step2.preserves_density dense3

theorem dense1 : RationallyDenseSystem E1 U1 := by
  apply dense_system_of_factor_reductions E1 R1 U1 reductions1
  exact step1.preserves_density dense2

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  exact step0.preserves_density dense1

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart563Omit0
end

/- Source: ChartTables/Case563Omit0.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart563Omit0
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Option (Option (Option (Option (Fin 0))))))) :=
  ![![.one, .one, .one, .zero], ![.one, .zero, .variable (some (some (none))), .one], ![.one, .variable (none), .zero, .variable (some (none))], ![.variable (some (some (some (some (none))))), .one, .variable (some (some (some (none)))), .variable (some (some (some (some (some (none))))))]]

noncomputable def chartPositions : (Option (Option (Option (Option (Option (Option (Fin 0))))))) → Coordinate × Coordinate :=
  Option.elim' (2, 1) (Option.elim' (2, 3) (Option.elim' (1, 2) (Option.elim' (3, 2) (Option.elim' (3, 0) (Option.elim' (3, 3) ![])))))

noncomputable def chartUnitVariables : Fin 5 → (Option (Option (Option (Option (Option (Option (Fin 0))))))) :=
  ![some (some (none)), none, some (none), some (some (some (none))), some (some (some (some (some (none)))))]

noncomputable def chartLabelCode : ℕ := 16434824

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, false, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, false, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false, true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Option (Option (Option (Option (Fin 0))))))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 563)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 563) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨13, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70)
      rw [minorFormula_at_13]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨24, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (24 : Fin 70)
      rw [minorFormula_at_24]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨45, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70)
      rw [minorFormula_at_45]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨61, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70)
      rw [minorFormula_at_61]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨67, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (67 : Fin 70)
      rw [minorFormula_at_67]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (7 : Fin 70) = _
      rw [minorFormula_at_7]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70)
      rw [minorFormula_at_13]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (16 : Fin 70) = _
      rw [minorFormula_at_16]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨1, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (24 : Fin 70)
      rw [minorFormula_at_24]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (38 : Fin 70) = _
      rw [minorFormula_at_38]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨2, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70)
      rw [minorFormula_at_45]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨3, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70)
      rw [minorFormula_at_61]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨4, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (67 : Fin 70)
      rw [minorFormula_at_67]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(4,1),(4,2),(5,3),(1,7)]

theorem chart_schedule : Papers.MatrixGaugeNormalization.checkSchedule chartForestRoots chartForestSteps = true := by
  decide +kernel

theorem chart_steps_are_ones : ∀ e ∈ chartForestSteps,
    (∃ i j : Coordinate, e = (firstFour i, lastFour j) ∧ chartEntries i j = .one) ∨
    (∃ i j : Coordinate, e = (lastFour j, firstFour i) ∧ chartEntries i j = .one) := by
  decide +kernel

theorem chart_ones_are_steps : ∀ i j : Coordinate, chartEntries i j = .one →
    (firstFour i, lastFour j) ∈ chartForestSteps ∨
    (lastFour j, firstFour i) ∈ chartForestSteps := by
  decide +kernel

noncomputable def chart_certificate : ChartCertificate (Option (Option (Option (Option (Option (Option (Fin 0))))))) 5 5
    (MatroidCatalogue.N8R4.family 563) where
  entries := chartEntries
  positions := chartPositions
  unitVariables := chartUnitVariables
  labelCode := chartLabelCode
  basisMark := chartBasisMark
  requiredZero := chartRequiredZero
  polynomials := chartMinorPolynomials
  equations := E0
  units := U0
  roots := chartForestRoots
  steps := chartForestSteps
  parameters := chart_parameters
  minors := chart_minors
  pattern := chart_pattern
  first_basis := chart_first_basis
  constraints := chart_entry_constraints
  equation_table := chart_equations
  units_exact := chart_units_exact
  required_nonbasis := chart_required_nonbasis
  schedule := chart_schedule
  steps_are_ones := chart_steps_are_ones
  ones_are_steps := chart_ones_are_steps

noncomputable def omittedFourSet : Finset Point := {0,1,2,4}

theorem chart_required_except : ∀ i, chartBasisMark i ≠ true →
    minorSet i ≠ omittedFourSet → chartRequiredZero i = true := by
  decide +kernel

theorem chart_omitted_label : omittedFourSet.image
    (BasisCertificates.checkedPermutation 8 chartLabelCode chart_pattern.permutation_valid) =
    ({0,1,2,4} : Finset Point) := by
  decide +kernel

/-- The omitted nonbasis is specified using the actual catalogue labels. -/
theorem family_selected_density {n : ℕ}
    (p : Matrix Point Coordinate ℝ)
    (hp : MatroidChecked.GoldenSelectedRanks.Golden p)
    (σ : Equiv.Perm Point)
    (hcatalogue : (VectorBasisFamilies.vectorBases p).image (fun S => S.image σ) =
      MatroidCatalogue.N8R4.family 563)
    (Z : Fin n → Finset Point)
    (havoid : ∀ j, (Z j).image σ ≠ ({0,1,2,4} : Finset Point)) :
    p ∈ closure (ChirotopeDensity.SelectedRankRealizations p Z) := by
  apply MatroidChecked.GoldenSelectedRanks.ChartCertificate.selected_density_of_omission
    chart_certificate rationally_dense p hp σ hcatalogue omittedFourSet
    chart_required_except Z
  change ∀ j, (Z j).image σ ≠ omittedFourSet.image
    (BasisCertificates.checkedPermutation 8 chartLabelCode chart_pattern.permutation_valid)
  rw [chart_omitted_label]
  exact havoid

end Papers.RationalityTen.Chart563Omit0
end

/- Source: Charts/Case563Omit1.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart563Omit1
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Fin 1)))))) ℚ :=
  ![X (none) * X (some (some (some (some (none))))) - (X (some (none))), -(X (some (some (none))) * X (some (some (some (some (none)))))) + (X (some (some (some (none))))), -(X (none)) + (1), -(X (some (some (none)))) - (X (some (some (some (none))))) + (1), -(X (some (none)) * X (some (some (none)))) + (X (some (none))) + (X (some (some (some (some (some (0 : Fin 1))))))) - (1)]
noncomputable def U0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Fin 1)))))) ℚ :=
  ![X (some (some (none))), X (none), X (some (none)), X (some (some (some (none)))), X (some (some (some (some (none)))))]
noncomputable def R0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Fin 1)))))) ℚ :=
  ![X (none) * X (some (some (some (some (none))))) - (X (some (none))), X (some (some (none))) * X (some (some (some (some (none))))) - (X (some (some (some (none))))), X (none) - (1), X (some (some (none))) + (X (some (some (some (none))))) - (1), X (some (none)) * X (some (some (none))) - (X (some (none))) - (X (some (some (some (some (some (0 : Fin 1))))))) + (1)]

noncomputable def reductions0 (j : Fin 5) : FactorReduction U0 (E0 j) (R0 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring

noncomputable def nextE0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 1))))) ℚ :=
  ![-(X (none)) + (X (some (some (some (none))))), X (some (none)) * X (some (some (some (none)))) - (X (some (some (none)))), 0, X (some (none)) + (X (some (some (none)))) - (1), X (none) * X (some (none)) - (X (none)) - (X (some (some (some (some (0 : Fin 1)))))) + (1)]
noncomputable def nextU0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 1))))) ℚ :=
  ![X (some (none)), 1, X (none), X (some (some (none))), X (some (some (some (none))))]

noncomputable def step0 : LinearStep (Option (Option (Option (Option (Fin 1))))) 5 5 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := 1
  b := -(1)
  pivot := 2
  pivot_identity := by simp [R0]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 0, 1, 0, 0]
  equation_quotient := ![X (some (some (some (some (none))))), 0, 1, 0, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![0, 1, 0, 0, 0]
  unit_quotient := ![0, 1, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 1))))) ℚ :=
  ![-(X (none)) + (X (some (some (some (none))))), X (some (none)) * X (some (some (some (none)))) - (X (some (some (none)))), 0, X (some (none)) + (X (some (some (none)))) - (1), X (none) * X (some (none)) - (X (none)) - (X (some (some (some (some (0 : Fin 1)))))) + (1)]
noncomputable def U1 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 1))))) ℚ :=
  ![X (some (none)), 1, X (none), X (some (some (none))), X (some (some (some (none))))]
noncomputable def R1 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 1))))) ℚ :=
  ![X (none) - (X (some (some (some (none))))), X (some (none)) * X (some (some (some (none)))) - (X (some (some (none)))), 0, X (some (none)) + (X (some (some (none)))) - (1), X (none) * X (some (none)) - (X (none)) - (X (some (some (some (some (0 : Fin 1)))))) + (1)]

noncomputable def reductions1 (j : Fin 5) : FactorReduction U1 (E1 j) (R1 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring

noncomputable def nextE1 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 1)))) ℚ :=
  ![0, X (none) * X (some (some (none))) - (X (some (none))), 0, X (none) + (X (some (none))) - (1), X (none) * X (some (some (none))) - (X (some (some (none)))) - (X (some (some (some (0 : Fin 1))))) + (1)]
noncomputable def nextU1 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 1)))) ℚ :=
  ![X (none), 1, X (some (some (none))), X (some (none)), X (some (some (none)))]

noncomputable def step1 : LinearStep (Option (Option (Option (Fin 1)))) 5 5 where
  sourceE := R1
  sourceU := U1
  targetE := nextE1
  targetU := nextU1
  a := 1
  b := -(X (some (some (none))))
  pivot := 0
  pivot_identity := by simp [R1]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 0, 0, 0, 1]
  equation_quotient := ![1, 0, 0, 0, X (some (none)) - (1)]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring
  unit_power := ![0, 0, 1, 0, 0]
  unit_quotient := ![0, 0, 1, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring

noncomputable def E2 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 1)))) ℚ :=
  ![0, X (none) * X (some (some (none))) - (X (some (none))), 0, X (none) + (X (some (none))) - (1), X (none) * X (some (some (none))) - (X (some (some (none)))) - (X (some (some (some (0 : Fin 1))))) + (1)]
noncomputable def U2 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 1)))) ℚ :=
  ![X (none), 1, X (some (some (none))), X (some (none)), X (some (some (none)))]
noncomputable def R2 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 1)))) ℚ :=
  ![0, X (none) * X (some (some (none))) - (X (some (none))), 0, X (none) + (X (some (none))) - (1), X (none) * X (some (some (none))) - (X (some (some (none)))) - (X (some (some (some (0 : Fin 1))))) + (1)]

noncomputable def reductions2 (j : Fin 5) : FactorReduction U2 (E2 j) (R2 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring

noncomputable def nextE2 : Fin 5 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![0, -(X (none) * X (some (none))) - (X (none)) + (X (some (none))), 0, 0, -(X (none) * X (some (none))) - (X (some (some (0 : Fin 1)))) + (1)]
noncomputable def nextU2 : Fin 5 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![-(X (none)) + (1), 1, X (some (none)), X (none), X (some (none))]

noncomputable def step2 : LinearStep (Option (Option (Fin 1))) 5 5 where
  sourceE := R2
  sourceU := U2
  targetE := nextE2
  targetU := nextU2
  a := 1
  b := X (none) - (1)
  pivot := 3
  pivot_identity := by simp [R2]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 1, 0, 1, 1]
  equation_quotient := ![0, X (some (some (none))), 0, 1, X (some (some (none)))]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring
  unit_power := ![1, 0, 0, 0, 0]
  unit_quotient := ![1, 0, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring

noncomputable def E3 : Fin 5 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![0, -(X (none) * X (some (none))) - (X (none)) + (X (some (none))), 0, 0, -(X (none) * X (some (none))) - (X (some (some (0 : Fin 1)))) + (1)]
noncomputable def U3 : Fin 5 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![-(X (none)) + (1), 1, X (some (none)), X (none), X (some (none))]
noncomputable def R3 : Fin 5 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![0, X (none) * X (some (none)) + (X (none)) - (X (some (none))), 0, 0, X (none) * X (some (none)) + (X (some (some (0 : Fin 1)))) - (1)]

noncomputable def reductions3 (j : Fin 5) : FactorReduction U3 (E3 j) (R3 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring

noncomputable def nextE3 : Fin 5 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![0, 0, 0, 0, (X (none)) ^ 2 + (X (none) * X (some (0 : Fin 1))) - (X (none)) + (X (some (0 : Fin 1))) - (1)]
noncomputable def nextU3 : Fin 5 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![1, 1, X (none), X (none), X (none)]

noncomputable def step3 : LinearStep (Option (Fin 1)) 5 5 where
  sourceE := R3
  sourceU := U3
  targetE := nextE3
  targetU := nextU3
  a := X (none) + (1)
  b := -(X (none))
  pivot := 1
  pivot_identity := by simp [R3]<;> ring
  coefficient_or_constant_unit := Sum.inr {
      count := 1
      selected := ![2]
      quotient := -(1)
      identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 1, 0, 0, 1]
  equation_quotient := ![0, X (some (none)) + (1), 0, 0, X (some (none))]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R3, U3, nextE3, nextU3, map_ofNat] <;> ring
  unit_power := ![1, 0, 0, 1, 0]
  unit_quotient := ![-(1), 0, 0, 1, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R3, U3, nextE3, nextU3, map_ofNat] <;> ring

noncomputable def E4 : Fin 5 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![0, 0, 0, 0, (X (none)) ^ 2 + (X (none) * X (some (0 : Fin 1))) - (X (none)) + (X (some (0 : Fin 1))) - (1)]
noncomputable def U4 : Fin 5 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![1, 1, X (none), X (none), X (none)]
noncomputable def R4 : Fin 5 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![0, 0, 0, 0, (X (none)) ^ 2 + (X (none) * X (some (0 : Fin 1))) - (X (none)) + (X (some (0 : Fin 1))) - (1)]

noncomputable def reductions4 (j : Fin 5) : FactorReduction U4 (E4 j) (R4 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring

noncomputable def residual : MvPolynomial (Option (Fin 1)) ℚ := (X (none)) ^ 2 + (X (none) * X (some (0 : Fin 1))) - (X (none)) + (X (some (0 : Fin 1))) - (1)

noncomputable def factor0 : MvPolynomial (Option (Fin 1)) ℚ := (X (none)) ^ 2 + (X (none) * X (some (0 : Fin 1))) - (X (none)) + (X (some (0 : Fin 1))) - (1)

theorem factor0_density (x : (Option (Fin 1)) → ℝ)
    (hx : evalRat factor0 x = 0) :
    x ∈ closure {q | RationalVector q ∧ evalRat factor0 q = 0} := by
  have haffine : ∀ i : Fin 1, AffineIn (evalRat factor0) (some i) := by
    intro i; fin_cases i <;> intro q t <;>
      simp [factor0, evalRat, axisSlope] <;> ring
  apply AlgebraicChartDensity.multiaffine_density_of_affine_bezout factor0
    haffine x hx (![![0], ![1]]) (![x none - (1), -(x none) + (2)])
  norm_num [factor0, evalRat, Fin.sum_univ_succ] <;> ring

theorem residual_density (x : (Option (Fin 1)) → ℝ)
    (hx : evalRat residual x = 0) :
    x ∈ closure {q | RationalVector q ∧ evalRat residual q = 0} := by
  exact factor0_density x hx

theorem dense4 : RationallyDenseSystem E4 U4 := by
  apply dense_system_of_factor_reductions E4 R4 U4 reductions4
  apply system_dense_of_single_equation R4 U4 residual 4
    (by rfl) (![0, 0, 0, 0, 1]) ?_ residual_density
  intro j; fin_cases j <;> simp [R4, residual] <;> ring

theorem dense3 : RationallyDenseSystem E3 U3 := by
  apply dense_system_of_factor_reductions E3 R3 U3 reductions3
  exact step3.preserves_density dense4

theorem dense2 : RationallyDenseSystem E2 U2 := by
  apply dense_system_of_factor_reductions E2 R2 U2 reductions2
  exact step2.preserves_density dense3

theorem dense1 : RationallyDenseSystem E1 U1 := by
  apply dense_system_of_factor_reductions E1 R1 U1 reductions1
  exact step1.preserves_density dense2

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  exact step0.preserves_density dense1

/-- Rational density, with every residual component treated. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart563Omit1
end

/- Source: ChartTables/Case563Omit1.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart563Omit1
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Option (Option (Option (Fin 1)))))) :=
  ![![.one, .one, .one, .zero], ![.one, .zero, .variable (some (some (none))), .one], ![.one, .variable (none), .variable (some (some (some (some (some (0 : Fin 1)))))), .variable (some (none))], ![.zero, .one, .variable (some (some (some (none)))), .variable (some (some (some (some (none)))))]]

noncomputable def chartPositions : (Option (Option (Option (Option (Option (Fin 1)))))) → Coordinate × Coordinate :=
  Option.elim' (2, 1) (Option.elim' (2, 3) (Option.elim' (1, 2) (Option.elim' (3, 2) (Option.elim' (3, 3) ![(2, 2)]))))

noncomputable def chartUnitVariables : Fin 5 → (Option (Option (Option (Option (Option (Fin 1)))))) :=
  ![some (some (none)), none, some (none), some (some (some (none))), some (some (some (some (none))))]

noncomputable def chartLabelCode : ℕ := 16434824

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, false, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, false, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, false, false, false, false, false, false, false, false, false, false, false, true, false, false, true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Option (Option (Option (Fin 1)))))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 563)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 563) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨13, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70)
      rw [minorFormula_at_13]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨24, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (24 : Fin 70)
      rw [minorFormula_at_24]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨45, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70)
      rw [minorFormula_at_45]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨61, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70)
      rw [minorFormula_at_61]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨67, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (67 : Fin 70)
      rw [minorFormula_at_67]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (1 : Fin 70) = _
      rw [minorFormula_at_1]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70)
      rw [minorFormula_at_13]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (16 : Fin 70) = _
      rw [minorFormula_at_16]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨1, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (24 : Fin 70)
      rw [minorFormula_at_24]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (38 : Fin 70) = _
      rw [minorFormula_at_38]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨2, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70)
      rw [minorFormula_at_45]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨3, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70)
      rw [minorFormula_at_61]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨4, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (67 : Fin 70)
      rw [minorFormula_at_67]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(4,1),(4,2),(5,3),(1,7)]

theorem chart_schedule : Papers.MatrixGaugeNormalization.checkSchedule chartForestRoots chartForestSteps = true := by
  decide +kernel

theorem chart_steps_are_ones : ∀ e ∈ chartForestSteps,
    (∃ i j : Coordinate, e = (firstFour i, lastFour j) ∧ chartEntries i j = .one) ∨
    (∃ i j : Coordinate, e = (lastFour j, firstFour i) ∧ chartEntries i j = .one) := by
  decide +kernel

theorem chart_ones_are_steps : ∀ i j : Coordinate, chartEntries i j = .one →
    (firstFour i, lastFour j) ∈ chartForestSteps ∨
    (lastFour j, firstFour i) ∈ chartForestSteps := by
  decide +kernel

noncomputable def chart_certificate : ChartCertificate (Option (Option (Option (Option (Option (Fin 1)))))) 5 5
    (MatroidCatalogue.N8R4.family 563) where
  entries := chartEntries
  positions := chartPositions
  unitVariables := chartUnitVariables
  labelCode := chartLabelCode
  basisMark := chartBasisMark
  requiredZero := chartRequiredZero
  polynomials := chartMinorPolynomials
  equations := E0
  units := U0
  roots := chartForestRoots
  steps := chartForestSteps
  parameters := chart_parameters
  minors := chart_minors
  pattern := chart_pattern
  first_basis := chart_first_basis
  constraints := chart_entry_constraints
  equation_table := chart_equations
  units_exact := chart_units_exact
  required_nonbasis := chart_required_nonbasis
  schedule := chart_schedule
  steps_are_ones := chart_steps_are_ones
  ones_are_steps := chart_ones_are_steps

noncomputable def omittedFourSet : Finset Point := {0,1,3,6}

theorem chart_required_except : ∀ i, chartBasisMark i ≠ true →
    minorSet i ≠ omittedFourSet → chartRequiredZero i = true := by
  decide +kernel

theorem chart_omitted_label : omittedFourSet.image
    (BasisCertificates.checkedPermutation 8 chartLabelCode chart_pattern.permutation_valid) =
    ({0,1,3,6} : Finset Point) := by
  decide +kernel

/-- The omitted nonbasis is specified using the actual catalogue labels. -/
theorem family_selected_density {n : ℕ}
    (p : Matrix Point Coordinate ℝ)
    (hp : MatroidChecked.GoldenSelectedRanks.Golden p)
    (σ : Equiv.Perm Point)
    (hcatalogue : (VectorBasisFamilies.vectorBases p).image (fun S => S.image σ) =
      MatroidCatalogue.N8R4.family 563)
    (Z : Fin n → Finset Point)
    (havoid : ∀ j, (Z j).image σ ≠ ({0,1,3,6} : Finset Point)) :
    p ∈ closure (ChirotopeDensity.SelectedRankRealizations p Z) := by
  apply MatroidChecked.GoldenSelectedRanks.ChartCertificate.selected_density_of_omission
    chart_certificate rationally_dense p hp σ hcatalogue omittedFourSet
    chart_required_except Z
  change ∀ j, (Z j).image σ ≠ omittedFourSet.image
    (BasisCertificates.checkedPermutation 8 chartLabelCode chart_pattern.permutation_valid)
  rw [chart_omitted_label]
  exact havoid

end Papers.RationalityTen.Chart563Omit1
end

/- Source: Charts/Case563Omit2.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart563Omit2
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![-(X (some (some (none))) * X (some (some (some (some (none)))))) + (X (some (some (some (none))))), -(X (none)) + (1), -(X (some (some (none)))) - (X (some (some (some (none))))) + (1), -(X (some (none)) * X (some (some (none)))) + (X (some (none))) - (1)]
noncomputable def U0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![X (some (some (none))), X (none), X (some (none)), X (some (some (some (none)))), X (some (some (some (some (none)))))]
noncomputable def R0 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![X (some (some (none))) * X (some (some (some (some (none))))) - (X (some (some (some (none))))), X (none) - (1), X (some (some (none))) + (X (some (some (some (none))))) - (1), X (some (none)) * X (some (some (none))) - (X (some (none))) + (1)]

noncomputable def reductions0 (j : Fin 4) : FactorReduction U0 (E0 j) (R0 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring

noncomputable def nextE0 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (some (none)) * X (some (some (some (none)))) - (X (some (some (none)))), 0, X (some (none)) + (X (some (some (none)))) - (1), X (none) * X (some (none)) - (X (none)) + (1)]
noncomputable def nextU0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (some (none)), 1, X (none), X (some (some (none))), X (some (some (some (none))))]

noncomputable def step0 : LinearStep (Option (Option (Option (Option (Fin 0))))) 4 5 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := 1
  b := -(1)
  pivot := 1
  pivot_identity := by simp [R0]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 1, 0, 0]
  equation_quotient := ![0, 1, 0, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![0, 1, 0, 0, 0]
  unit_quotient := ![0, 1, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (some (none)) * X (some (some (some (none)))) - (X (some (some (none)))), 0, X (some (none)) + (X (some (some (none)))) - (1), X (none) * X (some (none)) - (X (none)) + (1)]
noncomputable def U1 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (some (none)), 1, X (none), X (some (some (none))), X (some (some (some (none))))]
noncomputable def R1 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (some (none)) * X (some (some (some (none)))) - (X (some (some (none)))), 0, X (some (none)) + (X (some (some (none)))) - (1), X (none) * X (some (none)) - (X (none)) + (1)]

noncomputable def reductions1 (j : Fin 4) : FactorReduction U1 (E1 j) (R1 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring

noncomputable def nextE1 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none) * X (some (some (none))) - (X (some (none))), 0, X (none) + (X (some (none))) - (1), 0]
noncomputable def nextU1 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none), 1, -(1), X (some (none)), X (some (some (none)))]

noncomputable def step1 : LinearStep (Option (Option (Option (Fin 0)))) 4 5 where
  sourceE := R1
  sourceU := U1
  targetE := nextE1
  targetU := nextU1
  a := X (none) - (1)
  b := 1
  pivot := 3
  pivot_identity := by simp [R1]<;> ring
  coefficient_or_constant_unit := Sum.inr {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 0, 0, 1]
  equation_quotient := ![0, 0, 0, X (some (none)) - (1)]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring
  unit_power := ![0, 0, 1, 0, 0]
  unit_quotient := ![0, 0, 1, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring

noncomputable def E2 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none) * X (some (some (none))) - (X (some (none))), 0, X (none) + (X (some (none))) - (1), 0]
noncomputable def U2 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none), 1, -(1), X (some (none)), X (some (some (none)))]
noncomputable def R2 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none) * X (some (some (none))) - (X (some (none))), 0, X (none) + (X (some (none))) - (1), 0]

noncomputable def reductions2 (j : Fin 4) : FactorReduction U2 (E2 j) (R2 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring

noncomputable def nextE2 : Fin 4 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![-(X (none) * X (some (none))) - (X (none)) + (X (some (none))), 0, 0, 0]
noncomputable def nextU2 : Fin 5 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![-(X (none)) + (1), 1, -(1), X (none), X (some (none))]

noncomputable def step2 : LinearStep (Option (Option (Fin 0))) 4 5 where
  sourceE := R2
  sourceU := U2
  targetE := nextE2
  targetU := nextU2
  a := 1
  b := X (none) - (1)
  pivot := 2
  pivot_identity := by simp [R2]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 0, 1, 0]
  equation_quotient := ![X (some (some (none))), 0, 1, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring
  unit_power := ![1, 0, 0, 0, 0]
  unit_quotient := ![1, 0, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring

noncomputable def E3 : Fin 4 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![-(X (none) * X (some (none))) - (X (none)) + (X (some (none))), 0, 0, 0]
noncomputable def U3 : Fin 5 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![-(X (none)) + (1), 1, -(1), X (none), X (some (none))]
noncomputable def R3 : Fin 4 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none) * X (some (none)) + (X (none)) - (X (some (none))), 0, 0, 0]

noncomputable def reductions3 (j : Fin 4) : FactorReduction U3 (E3 j) (R3 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring

noncomputable def nextE3 : Fin 4 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0]
noncomputable def nextU3 : Fin 5 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![1, 1, -(1), X (none), X (none)]

noncomputable def step3 : LinearStep (Option (Fin 0)) 4 5 where
  sourceE := R3
  sourceU := U3
  targetE := nextE3
  targetU := nextU3
  a := X (none) + (1)
  b := -(X (none))
  pivot := 0
  pivot_identity := by simp [R3]<;> ring
  coefficient_or_constant_unit := Sum.inr {
      count := 1
      selected := ![4]
      quotient := -(1)
      identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 0, 0, 0]
  equation_quotient := ![X (some (none)) + (1), 0, 0, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R3, U3, nextE3, nextU3, map_ofNat] <;> ring
  unit_power := ![1, 0, 0, 1, 0]
  unit_quotient := ![-(1), 0, 0, 1, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R3, U3, nextE3, nextU3, map_ofNat] <;> ring

noncomputable def E4 : Fin 4 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0]
noncomputable def U4 : Fin 5 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![1, 1, -(1), X (none), X (none)]
noncomputable def R4 : Fin 4 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0]

noncomputable def reductions4 (j : Fin 4) : FactorReduction U4 (E4 j) (R4 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring

theorem dense4 : RationallyDenseSystem E4 U4 := by
  apply dense_system_of_factor_reductions E4 R4 U4 reductions4
  apply zero_equations_system_dense R4 U4
  intro j; fin_cases j <;> rfl

theorem dense3 : RationallyDenseSystem E3 U3 := by
  apply dense_system_of_factor_reductions E3 R3 U3 reductions3
  exact step3.preserves_density dense4

theorem dense2 : RationallyDenseSystem E2 U2 := by
  apply dense_system_of_factor_reductions E2 R2 U2 reductions2
  exact step2.preserves_density dense3

theorem dense1 : RationallyDenseSystem E1 U1 := by
  apply dense_system_of_factor_reductions E1 R1 U1 reductions1
  exact step1.preserves_density dense2

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  exact step0.preserves_density dense1

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart563Omit2
end

/- Source: ChartTables/Case563Omit2.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart563Omit2
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Option (Option (Option (Fin 0)))))) :=
  ![![.one, .one, .one, .zero], ![.one, .zero, .variable (some (some (none))), .one], ![.one, .variable (none), .zero, .variable (some (none))], ![.zero, .one, .variable (some (some (some (none)))), .variable (some (some (some (some (none)))))]]

noncomputable def chartPositions : (Option (Option (Option (Option (Option (Fin 0)))))) → Coordinate × Coordinate :=
  Option.elim' (2, 1) (Option.elim' (2, 3) (Option.elim' (1, 2) (Option.elim' (3, 2) (Option.elim' (3, 3) ![]))))

noncomputable def chartUnitVariables : Fin 5 → (Option (Option (Option (Option (Option (Fin 0)))))) :=
  ![some (some (none)), none, some (none), some (some (some (none))), some (some (some (some (none))))]

noncomputable def chartLabelCode : ℕ := 16434824

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, false, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, false, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, false, false, false, false, false, true, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 563)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 563) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨24, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (24 : Fin 70)
      rw [minorFormula_at_24]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨45, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70)
      rw [minorFormula_at_45]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨61, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70)
      rw [minorFormula_at_61]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨67, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (67 : Fin 70)
      rw [minorFormula_at_67]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (1 : Fin 70) = _
      rw [minorFormula_at_1]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (7 : Fin 70) = _
      rw [minorFormula_at_7]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (16 : Fin 70) = _
      rw [minorFormula_at_16]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (24 : Fin 70)
      rw [minorFormula_at_24]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (38 : Fin 70) = _
      rw [minorFormula_at_38]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨1, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70)
      rw [minorFormula_at_45]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨2, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70)
      rw [minorFormula_at_61]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨3, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (67 : Fin 70)
      rw [minorFormula_at_67]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(4,1),(4,2),(5,3),(1,7)]

theorem chart_schedule : Papers.MatrixGaugeNormalization.checkSchedule chartForestRoots chartForestSteps = true := by
  decide +kernel

theorem chart_steps_are_ones : ∀ e ∈ chartForestSteps,
    (∃ i j : Coordinate, e = (firstFour i, lastFour j) ∧ chartEntries i j = .one) ∨
    (∃ i j : Coordinate, e = (lastFour j, firstFour i) ∧ chartEntries i j = .one) := by
  decide +kernel

theorem chart_ones_are_steps : ∀ i j : Coordinate, chartEntries i j = .one →
    (firstFour i, lastFour j) ∈ chartForestSteps ∨
    (lastFour j, firstFour i) ∈ chartForestSteps := by
  decide +kernel

noncomputable def chart_certificate : ChartCertificate (Option (Option (Option (Option (Option (Fin 0)))))) 4 5
    (MatroidCatalogue.N8R4.family 563) where
  entries := chartEntries
  positions := chartPositions
  unitVariables := chartUnitVariables
  labelCode := chartLabelCode
  basisMark := chartBasisMark
  requiredZero := chartRequiredZero
  polynomials := chartMinorPolynomials
  equations := E0
  units := U0
  roots := chartForestRoots
  steps := chartForestSteps
  parameters := chart_parameters
  minors := chart_minors
  pattern := chart_pattern
  first_basis := chart_first_basis
  constraints := chart_entry_constraints
  equation_table := chart_equations
  units_exact := chart_units_exact
  required_nonbasis := chart_required_nonbasis
  schedule := chart_schedule
  steps_are_ones := chart_steps_are_ones
  ones_are_steps := chart_ones_are_steps

noncomputable def omittedFourSet : Finset Point := {0,1,5,7}

theorem chart_required_except : ∀ i, chartBasisMark i ≠ true →
    minorSet i ≠ omittedFourSet → chartRequiredZero i = true := by
  decide +kernel

theorem chart_omitted_label : omittedFourSet.image
    (BasisCertificates.checkedPermutation 8 chartLabelCode chart_pattern.permutation_valid) =
    ({0,1,5,7} : Finset Point) := by
  decide +kernel

/-- The omitted nonbasis is specified using the actual catalogue labels. -/
theorem family_selected_density {n : ℕ}
    (p : Matrix Point Coordinate ℝ)
    (hp : MatroidChecked.GoldenSelectedRanks.Golden p)
    (σ : Equiv.Perm Point)
    (hcatalogue : (VectorBasisFamilies.vectorBases p).image (fun S => S.image σ) =
      MatroidCatalogue.N8R4.family 563)
    (Z : Fin n → Finset Point)
    (havoid : ∀ j, (Z j).image σ ≠ ({0,1,5,7} : Finset Point)) :
    p ∈ closure (ChirotopeDensity.SelectedRankRealizations p Z) := by
  apply MatroidChecked.GoldenSelectedRanks.ChartCertificate.selected_density_of_omission
    chart_certificate rationally_dense p hp σ hcatalogue omittedFourSet
    chart_required_except Z
  change ∀ j, (Z j).image σ ≠ omittedFourSet.image
    (BasisCertificates.checkedPermutation 8 chartLabelCode chart_pattern.permutation_valid)
  rw [chart_omitted_label]
  exact havoid

end Papers.RationalityTen.Chart563Omit2
end

/- Source: Charts/Case563Omit3.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart563Omit3
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Fin 1)))))) ℚ :=
  ![X (none) * X (some (some (some (some (none))))) - (X (some (none))), -(X (some (some (none))) * X (some (some (some (some (none)))))) + (X (some (some (some (none))))), -(X (none)) + (1), -(X (some (some (none)))) + (X (some (some (some (none)))) * X (some (some (some (some (some (0 : Fin 1))))))) - (X (some (some (some (none))))) + (1), -(X (some (none)) * X (some (some (none)))) + (X (some (none))) - (1)]
noncomputable def U0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Fin 1)))))) ℚ :=
  ![X (some (some (none))), X (none), X (some (none)), X (some (some (some (none)))), X (some (some (some (some (none)))))]
noncomputable def R0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Fin 1)))))) ℚ :=
  ![X (none) * X (some (some (some (some (none))))) - (X (some (none))), X (some (some (none))) * X (some (some (some (some (none))))) - (X (some (some (some (none))))), X (none) - (1), X (some (some (none))) - (X (some (some (some (none)))) * X (some (some (some (some (some (0 : Fin 1))))))) + (X (some (some (some (none))))) - (1), X (some (none)) * X (some (some (none))) - (X (some (none))) + (1)]

noncomputable def reductions0 (j : Fin 5) : FactorReduction U0 (E0 j) (R0 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring

noncomputable def nextE0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 1))))) ℚ :=
  ![-(X (none)) + (X (some (some (some (none))))), X (some (none)) * X (some (some (some (none)))) - (X (some (some (none)))), 0, X (some (none)) - (X (some (some (none))) * X (some (some (some (some (0 : Fin 1)))))) + (X (some (some (none)))) - (1), X (none) * X (some (none)) - (X (none)) + (1)]
noncomputable def nextU0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 1))))) ℚ :=
  ![X (some (none)), 1, X (none), X (some (some (none))), X (some (some (some (none))))]

noncomputable def step0 : LinearStep (Option (Option (Option (Option (Fin 1))))) 5 5 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := 1
  b := -(1)
  pivot := 2
  pivot_identity := by simp [R0]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 0, 1, 0, 0]
  equation_quotient := ![X (some (some (some (some (none))))), 0, 1, 0, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![0, 1, 0, 0, 0]
  unit_quotient := ![0, 1, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 1))))) ℚ :=
  ![-(X (none)) + (X (some (some (some (none))))), X (some (none)) * X (some (some (some (none)))) - (X (some (some (none)))), 0, X (some (none)) - (X (some (some (none))) * X (some (some (some (some (0 : Fin 1)))))) + (X (some (some (none)))) - (1), X (none) * X (some (none)) - (X (none)) + (1)]
noncomputable def U1 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 1))))) ℚ :=
  ![X (some (none)), 1, X (none), X (some (some (none))), X (some (some (some (none))))]
noncomputable def R1 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 1))))) ℚ :=
  ![X (none) - (X (some (some (some (none))))), X (some (none)) * X (some (some (some (none)))) - (X (some (some (none)))), 0, X (some (none)) - (X (some (some (none))) * X (some (some (some (some (0 : Fin 1)))))) + (X (some (some (none)))) - (1), X (none) * X (some (none)) - (X (none)) + (1)]

noncomputable def reductions1 (j : Fin 5) : FactorReduction U1 (E1 j) (R1 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring

noncomputable def nextE1 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 1)))) ℚ :=
  ![0, X (none) * X (some (some (none))) - (X (some (none))), 0, X (none) - (X (some (none)) * X (some (some (some (0 : Fin 1))))) + (X (some (none))) - (1), X (none) * X (some (some (none))) - (X (some (some (none)))) + (1)]
noncomputable def nextU1 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 1)))) ℚ :=
  ![X (none), 1, X (some (some (none))), X (some (none)), X (some (some (none)))]

noncomputable def step1 : LinearStep (Option (Option (Option (Fin 1)))) 5 5 where
  sourceE := R1
  sourceU := U1
  targetE := nextE1
  targetU := nextU1
  a := 1
  b := -(X (some (some (none))))
  pivot := 0
  pivot_identity := by simp [R1]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 0, 0, 0, 1]
  equation_quotient := ![1, 0, 0, 0, X (some (none)) - (1)]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring
  unit_power := ![0, 0, 1, 0, 0]
  unit_quotient := ![0, 0, 1, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring

noncomputable def E2 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 1)))) ℚ :=
  ![0, X (none) * X (some (some (none))) - (X (some (none))), 0, X (none) - (X (some (none)) * X (some (some (some (0 : Fin 1))))) + (X (some (none))) - (1), X (none) * X (some (some (none))) - (X (some (some (none)))) + (1)]
noncomputable def U2 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 1)))) ℚ :=
  ![X (none), 1, X (some (some (none))), X (some (none)), X (some (some (none)))]
noncomputable def R2 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 1)))) ℚ :=
  ![0, X (none) * X (some (some (none))) - (X (some (none))), 0, X (none) - (X (some (none)) * X (some (some (some (0 : Fin 1))))) + (X (some (none))) - (1), X (none) * X (some (some (none))) - (X (some (some (none)))) + (1)]

noncomputable def reductions2 (j : Fin 5) : FactorReduction U2 (E2 j) (R2 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring

noncomputable def nextE2 : Fin 5 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![0, X (none) * X (some (none)) * X (some (some (0 : Fin 1))) - (X (none) * X (some (none))) - (X (none)) + (X (some (none))), 0, 0, X (none) * X (some (none)) * X (some (some (0 : Fin 1))) - (X (none) * X (some (none))) + (1)]
noncomputable def nextU2 : Fin 5 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![X (none) * X (some (some (0 : Fin 1))) - (X (none)) + (1), 1, X (some (none)), X (none), X (some (none))]

noncomputable def step2 : LinearStep (Option (Option (Fin 1))) 5 5 where
  sourceE := R2
  sourceU := U2
  targetE := nextE2
  targetU := nextU2
  a := 1
  b := -(X (none) * X (some (some (0 : Fin 1)))) + (X (none)) - (1)
  pivot := 3
  pivot_identity := by simp [R2]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 1, 0, 1, 1]
  equation_quotient := ![0, X (some (some (none))), 0, 1, X (some (some (none)))]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring
  unit_power := ![1, 0, 0, 0, 0]
  unit_quotient := ![1, 0, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring

noncomputable def E3 : Fin 5 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![0, X (none) * X (some (none)) * X (some (some (0 : Fin 1))) - (X (none) * X (some (none))) - (X (none)) + (X (some (none))), 0, 0, X (none) * X (some (none)) * X (some (some (0 : Fin 1))) - (X (none) * X (some (none))) + (1)]
noncomputable def U3 : Fin 5 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![X (none) * X (some (some (0 : Fin 1))) - (X (none)) + (1), 1, X (some (none)), X (none), X (some (none))]
noncomputable def R3 : Fin 5 → MvPolynomial (Option (Option (Fin 1))) ℚ :=
  ![0, X (none) * X (some (none)) * X (some (some (0 : Fin 1))) - (X (none) * X (some (none))) - (X (none)) + (X (some (none))), 0, 0, X (none) * X (some (none)) * X (some (some (0 : Fin 1))) - (X (none) * X (some (none))) + (1)]

noncomputable def reductions3 (j : Fin 5) : FactorReduction U3 (E3 j) (R3 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring

noncomputable def nextE3 : Fin 5 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![0, 0, 0, 0, -((X (none)) ^ 2 * X (some (0 : Fin 1))) + ((X (none)) ^ 2) + (X (none) * X (some (0 : Fin 1))) - (X (none)) - (1)]
noncomputable def nextU3 : Fin 5 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![-(1), 1, X (none), -(X (none)), X (none)]

noncomputable def step3 : LinearStep (Option (Fin 1)) 5 5 where
  sourceE := R3
  sourceU := U3
  targetE := nextE3
  targetU := nextU3
  a := X (none) * X (some (0 : Fin 1)) - (X (none)) - (1)
  b := X (none)
  pivot := 1
  pivot_identity := by simp [R3]<;> ring
  coefficient_or_constant_unit := Sum.inr {
      count := 1
      selected := ![2]
      quotient := 1
      identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 1, 0, 0, 1]
  equation_quotient := ![0, X (some (none)) * X (some (some (0 : Fin 1))) - (X (some (none))) - (1), 0, 0, X (some (none)) * X (some (some (0 : Fin 1))) - (X (some (none)))]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R3, U3, nextE3, nextU3, map_ofNat] <;> ring
  unit_power := ![1, 0, 0, 1, 0]
  unit_quotient := ![X (some (some (0 : Fin 1))) - (1), 0, 0, 1, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R3, U3, nextE3, nextU3, map_ofNat] <;> ring

noncomputable def E4 : Fin 5 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![0, 0, 0, 0, -((X (none)) ^ 2 * X (some (0 : Fin 1))) + ((X (none)) ^ 2) + (X (none) * X (some (0 : Fin 1))) - (X (none)) - (1)]
noncomputable def U4 : Fin 5 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![-(1), 1, X (none), -(X (none)), X (none)]
noncomputable def R4 : Fin 5 → MvPolynomial (Option (Fin 1)) ℚ :=
  ![0, 0, 0, 0, (X (none)) ^ 2 * X (some (0 : Fin 1)) - ((X (none)) ^ 2) - (X (none) * X (some (0 : Fin 1))) + (X (none)) + (1)]

noncomputable def reductions4 (j : Fin 5) : FactorReduction U4 (E4 j) (R4 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring

noncomputable def residual : MvPolynomial (Option (Fin 1)) ℚ := (X (none)) ^ 2 * X (some (0 : Fin 1)) - ((X (none)) ^ 2) - (X (none) * X (some (0 : Fin 1))) + (X (none)) + (1)

noncomputable def factor0 : MvPolynomial (Option (Fin 1)) ℚ := (X (none)) ^ 2 * X (some (0 : Fin 1)) - ((X (none)) ^ 2) - (X (none) * X (some (0 : Fin 1))) + (X (none)) + (1)

theorem factor0_density (x : (Option (Fin 1)) → ℝ)
    (hx : evalRat factor0 x = 0) :
    x ∈ closure {q | RationalVector q ∧ evalRat factor0 q = 0} := by
  have haffine : ∀ i : Fin 1, AffineIn (evalRat factor0) (some i) := by
    intro i; fin_cases i <;> intro q t <;>
      simp [factor0, evalRat, axisSlope] <;> ring
  apply AlgebraicChartDensity.multiaffine_density_of_affine_bezout factor0
    haffine x hx (![![1]]) (![1])
  norm_num [factor0, evalRat, Fin.sum_univ_succ] <;> ring

theorem residual_density (x : (Option (Fin 1)) → ℝ)
    (hx : evalRat residual x = 0) :
    x ∈ closure {q | RationalVector q ∧ evalRat residual q = 0} := by
  exact factor0_density x hx

theorem dense4 : RationallyDenseSystem E4 U4 := by
  apply dense_system_of_factor_reductions E4 R4 U4 reductions4
  apply system_dense_of_single_equation R4 U4 residual 4
    (by rfl) (![0, 0, 0, 0, 1]) ?_ residual_density
  intro j; fin_cases j <;> simp [R4, residual] <;> ring

theorem dense3 : RationallyDenseSystem E3 U3 := by
  apply dense_system_of_factor_reductions E3 R3 U3 reductions3
  exact step3.preserves_density dense4

theorem dense2 : RationallyDenseSystem E2 U2 := by
  apply dense_system_of_factor_reductions E2 R2 U2 reductions2
  exact step2.preserves_density dense3

theorem dense1 : RationallyDenseSystem E1 U1 := by
  apply dense_system_of_factor_reductions E1 R1 U1 reductions1
  exact step1.preserves_density dense2

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  exact step0.preserves_density dense1

/-- Rational density, with every residual component treated. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart563Omit3
end

/- Source: ChartTables/Case563Omit3.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart563Omit3
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Option (Option (Option (Fin 1)))))) :=
  ![![.one, .one, .one, .zero], ![.one, .variable (some (some (some (some (some (0 : Fin 1)))))), .variable (some (some (none))), .one], ![.one, .variable (none), .zero, .variable (some (none))], ![.zero, .one, .variable (some (some (some (none)))), .variable (some (some (some (some (none)))))]]

noncomputable def chartPositions : (Option (Option (Option (Option (Option (Fin 1)))))) → Coordinate × Coordinate :=
  Option.elim' (2, 1) (Option.elim' (2, 3) (Option.elim' (1, 2) (Option.elim' (3, 2) (Option.elim' (3, 3) ![(1, 1)]))))

noncomputable def chartUnitVariables : Fin 5 → (Option (Option (Option (Option (Option (Fin 1)))))) :=
  ![some (some (none)), none, some (none), some (some (some (none))), some (some (some (some (none))))]

noncomputable def chartLabelCode : ℕ := 16434824

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, false, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, false, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Option (Option (Option (Fin 1)))))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 563)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 563) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨13, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70)
      rw [minorFormula_at_13]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨24, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (24 : Fin 70)
      rw [minorFormula_at_24]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨45, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70)
      rw [minorFormula_at_45]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨61, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70)
      rw [minorFormula_at_61]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨67, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (67 : Fin 70)
      rw [minorFormula_at_67]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (1 : Fin 70) = _
      rw [minorFormula_at_1]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (7 : Fin 70) = _
      rw [minorFormula_at_7]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70)
      rw [minorFormula_at_13]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨1, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (24 : Fin 70)
      rw [minorFormula_at_24]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (38 : Fin 70) = _
      rw [minorFormula_at_38]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨2, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70)
      rw [minorFormula_at_45]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨3, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70)
      rw [minorFormula_at_61]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨4, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (67 : Fin 70)
      rw [minorFormula_at_67]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(4,1),(4,2),(5,3),(1,7)]

theorem chart_schedule : Papers.MatrixGaugeNormalization.checkSchedule chartForestRoots chartForestSteps = true := by
  decide +kernel

theorem chart_steps_are_ones : ∀ e ∈ chartForestSteps,
    (∃ i j : Coordinate, e = (firstFour i, lastFour j) ∧ chartEntries i j = .one) ∨
    (∃ i j : Coordinate, e = (lastFour j, firstFour i) ∧ chartEntries i j = .one) := by
  decide +kernel

theorem chart_ones_are_steps : ∀ i j : Coordinate, chartEntries i j = .one →
    (firstFour i, lastFour j) ∈ chartForestSteps ∨
    (lastFour j, firstFour i) ∈ chartForestSteps := by
  decide +kernel

noncomputable def chart_certificate : ChartCertificate (Option (Option (Option (Option (Option (Fin 1)))))) 5 5
    (MatroidCatalogue.N8R4.family 563) where
  entries := chartEntries
  positions := chartPositions
  unitVariables := chartUnitVariables
  labelCode := chartLabelCode
  basisMark := chartBasisMark
  requiredZero := chartRequiredZero
  polynomials := chartMinorPolynomials
  equations := E0
  units := U0
  roots := chartForestRoots
  steps := chartForestSteps
  parameters := chart_parameters
  minors := chart_minors
  pattern := chart_pattern
  first_basis := chart_first_basis
  constraints := chart_entry_constraints
  equation_table := chart_equations
  units_exact := chart_units_exact
  required_nonbasis := chart_required_nonbasis
  schedule := chart_schedule
  steps_are_ones := chart_steps_are_ones
  ones_are_steps := chart_ones_are_steps

noncomputable def omittedFourSet : Finset Point := {0,2,3,5}

theorem chart_required_except : ∀ i, chartBasisMark i ≠ true →
    minorSet i ≠ omittedFourSet → chartRequiredZero i = true := by
  decide +kernel

theorem chart_omitted_label : omittedFourSet.image
    (BasisCertificates.checkedPermutation 8 chartLabelCode chart_pattern.permutation_valid) =
    ({0,2,3,5} : Finset Point) := by
  decide +kernel

/-- The omitted nonbasis is specified using the actual catalogue labels. -/
theorem family_selected_density {n : ℕ}
    (p : Matrix Point Coordinate ℝ)
    (hp : MatroidChecked.GoldenSelectedRanks.Golden p)
    (σ : Equiv.Perm Point)
    (hcatalogue : (VectorBasisFamilies.vectorBases p).image (fun S => S.image σ) =
      MatroidCatalogue.N8R4.family 563)
    (Z : Fin n → Finset Point)
    (havoid : ∀ j, (Z j).image σ ≠ ({0,2,3,5} : Finset Point)) :
    p ∈ closure (ChirotopeDensity.SelectedRankRealizations p Z) := by
  apply MatroidChecked.GoldenSelectedRanks.ChartCertificate.selected_density_of_omission
    chart_certificate rationally_dense p hp σ hcatalogue omittedFourSet
    chart_required_except Z
  change ∀ j, (Z j).image σ ≠ omittedFourSet.image
    (BasisCertificates.checkedPermutation 8 chartLabelCode chart_pattern.permutation_valid)
  rw [chart_omitted_label]
  exact havoid

end Papers.RationalityTen.Chart563Omit3
end

/- Source: Charts/Case563Omit4.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart563Omit4
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![X (none) * X (some (some (some (some (none))))) - (X (some (none))), -(X (none)) + (1), -(X (some (some (none)))) - (X (some (some (some (none))))) + (1), -(X (some (none)) * X (some (some (none)))) + (X (some (none))) - (1)]
noncomputable def U0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![X (some (some (none))), X (none), X (some (none)), X (some (some (some (none)))), X (some (some (some (some (none)))))]
noncomputable def R0 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![X (none) * X (some (some (some (some (none))))) - (X (some (none))), X (none) - (1), X (some (some (none))) + (X (some (some (some (none))))) - (1), X (some (none)) * X (some (some (none))) - (X (some (none))) + (1)]

noncomputable def reductions0 (j : Fin 4) : FactorReduction U0 (E0 j) (R0 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring

noncomputable def nextE0 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![-(X (none)) + (X (some (some (some (none))))), 0, X (some (none)) + (X (some (some (none)))) - (1), X (none) * X (some (none)) - (X (none)) + (1)]
noncomputable def nextU0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (some (none)), 1, X (none), X (some (some (none))), X (some (some (some (none))))]

noncomputable def step0 : LinearStep (Option (Option (Option (Option (Fin 0))))) 4 5 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := 1
  b := -(1)
  pivot := 1
  pivot_identity := by simp [R0]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 1, 0, 0]
  equation_quotient := ![X (some (some (some (some (none))))), 1, 0, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![0, 1, 0, 0, 0]
  unit_quotient := ![0, 1, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![-(X (none)) + (X (some (some (some (none))))), 0, X (some (none)) + (X (some (some (none)))) - (1), X (none) * X (some (none)) - (X (none)) + (1)]
noncomputable def U1 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (some (none)), 1, X (none), X (some (some (none))), X (some (some (some (none))))]
noncomputable def R1 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (none) - (X (some (some (some (none))))), 0, X (some (none)) + (X (some (some (none)))) - (1), X (none) * X (some (none)) - (X (none)) + (1)]

noncomputable def reductions1 (j : Fin 4) : FactorReduction U1 (E1 j) (R1 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring

noncomputable def nextE1 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![0, 0, X (none) + (X (some (none))) - (1), X (none) * X (some (some (none))) - (X (some (some (none)))) + (1)]
noncomputable def nextU1 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none), 1, X (some (some (none))), X (some (none)), X (some (some (none)))]

noncomputable def step1 : LinearStep (Option (Option (Option (Fin 0)))) 4 5 where
  sourceE := R1
  sourceU := U1
  targetE := nextE1
  targetU := nextU1
  a := 1
  b := -(X (some (some (none))))
  pivot := 0
  pivot_identity := by simp [R1]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 0, 0, 1]
  equation_quotient := ![1, 0, 0, X (some (none)) - (1)]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring
  unit_power := ![0, 0, 1, 0, 0]
  unit_quotient := ![0, 0, 1, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring

noncomputable def E2 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![0, 0, X (none) + (X (some (none))) - (1), X (none) * X (some (some (none))) - (X (some (some (none)))) + (1)]
noncomputable def U2 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none), 1, X (some (some (none))), X (some (none)), X (some (some (none)))]
noncomputable def R2 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![0, 0, X (none) + (X (some (none))) - (1), X (none) * X (some (some (none))) - (X (some (some (none)))) + (1)]

noncomputable def reductions2 (j : Fin 4) : FactorReduction U2 (E2 j) (R2 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring

noncomputable def nextE2 : Fin 4 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, 0, 0, -(X (none) * X (some (none))) + (1)]
noncomputable def nextU2 : Fin 5 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![-(X (none)) + (1), 1, X (some (none)), X (none), X (some (none))]

noncomputable def step2 : LinearStep (Option (Option (Fin 0))) 4 5 where
  sourceE := R2
  sourceU := U2
  targetE := nextE2
  targetU := nextU2
  a := 1
  b := X (none) - (1)
  pivot := 2
  pivot_identity := by simp [R2]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 0, 1, 1]
  equation_quotient := ![0, 0, 1, X (some (some (none)))]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring
  unit_power := ![1, 0, 0, 0, 0]
  unit_quotient := ![1, 0, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring

noncomputable def E3 : Fin 4 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, 0, 0, -(X (none) * X (some (none))) + (1)]
noncomputable def U3 : Fin 5 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![-(X (none)) + (1), 1, X (some (none)), X (none), X (some (none))]
noncomputable def R3 : Fin 4 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, 0, 0, X (none) * X (some (none)) - (1)]

noncomputable def reductions3 (j : Fin 4) : FactorReduction U3 (E3 j) (R3 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring

noncomputable def nextE3 : Fin 4 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0]
noncomputable def nextU3 : Fin 5 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none) - (1), 1, X (none), 1, X (none)]

noncomputable def step3 : LinearStep (Option (Fin 0)) 4 5 where
  sourceE := R3
  sourceU := U3
  targetE := nextE3
  targetU := nextU3
  a := X (none)
  b := -(1)
  pivot := 3
  pivot_identity := by simp [R3]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 1
      selected := ![2]
      quotient := 1
      identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 0, 0, 1]
  equation_quotient := ![0, 0, 0, X (some (none))]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R3, U3, nextE3, nextU3, map_ofNat] <;> ring
  unit_power := ![1, 0, 0, 1, 0]
  unit_quotient := ![-(1), 0, 0, 1, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R3, U3, nextE3, nextU3, map_ofNat] <;> ring

noncomputable def E4 : Fin 4 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0]
noncomputable def U4 : Fin 5 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none) - (1), 1, X (none), 1, X (none)]
noncomputable def R4 : Fin 4 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0]

noncomputable def reductions4 (j : Fin 4) : FactorReduction U4 (E4 j) (R4 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring

theorem dense4 : RationallyDenseSystem E4 U4 := by
  apply dense_system_of_factor_reductions E4 R4 U4 reductions4
  apply zero_equations_system_dense R4 U4
  intro j; fin_cases j <;> rfl

theorem dense3 : RationallyDenseSystem E3 U3 := by
  apply dense_system_of_factor_reductions E3 R3 U3 reductions3
  exact step3.preserves_density dense4

theorem dense2 : RationallyDenseSystem E2 U2 := by
  apply dense_system_of_factor_reductions E2 R2 U2 reductions2
  exact step2.preserves_density dense3

theorem dense1 : RationallyDenseSystem E1 U1 := by
  apply dense_system_of_factor_reductions E1 R1 U1 reductions1
  exact step1.preserves_density dense2

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  exact step0.preserves_density dense1

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart563Omit4
end

/- Source: ChartTables/Case563Omit4.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart563Omit4
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Option (Option (Option (Fin 0)))))) :=
  ![![.one, .one, .one, .zero], ![.one, .zero, .variable (some (some (none))), .one], ![.one, .variable (none), .zero, .variable (some (none))], ![.zero, .one, .variable (some (some (some (none)))), .variable (some (some (some (some (none)))))]]

noncomputable def chartPositions : (Option (Option (Option (Option (Option (Fin 0)))))) → Coordinate × Coordinate :=
  Option.elim' (2, 1) (Option.elim' (2, 3) (Option.elim' (1, 2) (Option.elim' (3, 2) (Option.elim' (3, 3) ![]))))

noncomputable def chartUnitVariables : Fin 5 → (Option (Option (Option (Option (Option (Fin 0)))))) :=
  ![some (some (none)), none, some (none), some (some (some (none))), some (some (some (some (none))))]

noncomputable def chartLabelCode : ℕ := 16434824

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, false, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, false, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, false, false, false, false, false, true, false, false, false, false, false, true, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 563)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 563) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨13, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70)
      rw [minorFormula_at_13]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨45, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70)
      rw [minorFormula_at_45]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨61, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70)
      rw [minorFormula_at_61]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨67, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (67 : Fin 70)
      rw [minorFormula_at_67]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (1 : Fin 70) = _
      rw [minorFormula_at_1]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (7 : Fin 70) = _
      rw [minorFormula_at_7]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70)
      rw [minorFormula_at_13]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (16 : Fin 70) = _
      rw [minorFormula_at_16]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (38 : Fin 70) = _
      rw [minorFormula_at_38]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨1, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70)
      rw [minorFormula_at_45]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨2, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70)
      rw [minorFormula_at_61]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨3, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (67 : Fin 70)
      rw [minorFormula_at_67]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(4,1),(4,2),(5,3),(1,7)]

theorem chart_schedule : Papers.MatrixGaugeNormalization.checkSchedule chartForestRoots chartForestSteps = true := by
  decide +kernel

theorem chart_steps_are_ones : ∀ e ∈ chartForestSteps,
    (∃ i j : Coordinate, e = (firstFour i, lastFour j) ∧ chartEntries i j = .one) ∨
    (∃ i j : Coordinate, e = (lastFour j, firstFour i) ∧ chartEntries i j = .one) := by
  decide +kernel

theorem chart_ones_are_steps : ∀ i j : Coordinate, chartEntries i j = .one →
    (firstFour i, lastFour j) ∈ chartForestSteps ∨
    (lastFour j, firstFour i) ∈ chartForestSteps := by
  decide +kernel

noncomputable def chart_certificate : ChartCertificate (Option (Option (Option (Option (Option (Fin 0)))))) 4 5
    (MatroidCatalogue.N8R4.family 563) where
  entries := chartEntries
  positions := chartPositions
  unitVariables := chartUnitVariables
  labelCode := chartLabelCode
  basisMark := chartBasisMark
  requiredZero := chartRequiredZero
  polynomials := chartMinorPolynomials
  equations := E0
  units := U0
  roots := chartForestRoots
  steps := chartForestSteps
  parameters := chart_parameters
  minors := chart_minors
  pattern := chart_pattern
  first_basis := chart_first_basis
  constraints := chart_entry_constraints
  equation_table := chart_equations
  units_exact := chart_units_exact
  required_nonbasis := chart_required_nonbasis
  schedule := chart_schedule
  steps_are_ones := chart_steps_are_ones
  ones_are_steps := chart_ones_are_steps

noncomputable def omittedFourSet : Finset Point := {0,2,6,7}

theorem chart_required_except : ∀ i, chartBasisMark i ≠ true →
    minorSet i ≠ omittedFourSet → chartRequiredZero i = true := by
  decide +kernel

theorem chart_omitted_label : omittedFourSet.image
    (BasisCertificates.checkedPermutation 8 chartLabelCode chart_pattern.permutation_valid) =
    ({0,2,6,7} : Finset Point) := by
  decide +kernel

/-- The omitted nonbasis is specified using the actual catalogue labels. -/
theorem family_selected_density {n : ℕ}
    (p : Matrix Point Coordinate ℝ)
    (hp : MatroidChecked.GoldenSelectedRanks.Golden p)
    (σ : Equiv.Perm Point)
    (hcatalogue : (VectorBasisFamilies.vectorBases p).image (fun S => S.image σ) =
      MatroidCatalogue.N8R4.family 563)
    (Z : Fin n → Finset Point)
    (havoid : ∀ j, (Z j).image σ ≠ ({0,2,6,7} : Finset Point)) :
    p ∈ closure (ChirotopeDensity.SelectedRankRealizations p Z) := by
  apply MatroidChecked.GoldenSelectedRanks.ChartCertificate.selected_density_of_omission
    chart_certificate rationally_dense p hp σ hcatalogue omittedFourSet
    chart_required_except Z
  change ∀ j, (Z j).image σ ≠ omittedFourSet.image
    (BasisCertificates.checkedPermutation 8 chartLabelCode chart_pattern.permutation_valid)
  rw [chart_omitted_label]
  exact havoid

end Papers.RationalityTen.Chart563Omit4
end

/- Source: Charts/Case563Omit5.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart563Omit5
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Option (Fin 0))))))) ℚ :=
  ![X (none) * X (some (some (some (some (some (none)))))) - (X (some (none))), -(X (some (some (none))) * X (some (some (some (some (some (none))))))) + (X (some (some (some (none))))), -(X (none)) + (1), -(X (some (some (none)))) - (X (some (some (some (none))))) + (1), -(X (some (none)) * X (some (some (none)))) + (X (some (none))) + (X (some (some (none))) * X (some (some (some (some (none)))))) - (1)]
noncomputable def U0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Option (Fin 0))))))) ℚ :=
  ![X (some (some (none))), X (none), X (some (none)), X (some (some (some (none)))), X (some (some (some (some (some (none))))))]
noncomputable def R0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Option (Fin 0))))))) ℚ :=
  ![X (none) * X (some (some (some (some (some (none)))))) - (X (some (none))), X (some (some (none))) * X (some (some (some (some (some (none)))))) - (X (some (some (some (none))))), X (none) - (1), X (some (some (none))) + (X (some (some (some (none))))) - (1), X (some (none)) * X (some (some (none))) - (X (some (none))) - (X (some (some (none))) * X (some (some (some (some (none)))))) + (1)]

noncomputable def reductions0 (j : Fin 5) : FactorReduction U0 (E0 j) (R0 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring

noncomputable def nextE0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![-(X (none)) + (X (some (some (some (some (none)))))), X (some (none)) * X (some (some (some (some (none))))) - (X (some (some (none)))), 0, X (some (none)) + (X (some (some (none)))) - (1), X (none) * X (some (none)) - (X (none)) - (X (some (none)) * X (some (some (some (none))))) + (1)]
noncomputable def nextU0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![X (some (none)), 1, X (none), X (some (some (none))), X (some (some (some (some (none)))))]

noncomputable def step0 : LinearStep (Option (Option (Option (Option (Option (Fin 0)))))) 5 5 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := 1
  b := -(1)
  pivot := 2
  pivot_identity := by simp [R0]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 0, 1, 0, 0]
  equation_quotient := ![X (some (some (some (some (some (none)))))), 0, 1, 0, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![0, 1, 0, 0, 0]
  unit_quotient := ![0, 1, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![-(X (none)) + (X (some (some (some (some (none)))))), X (some (none)) * X (some (some (some (some (none))))) - (X (some (some (none)))), 0, X (some (none)) + (X (some (some (none)))) - (1), X (none) * X (some (none)) - (X (none)) - (X (some (none)) * X (some (some (some (none))))) + (1)]
noncomputable def U1 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![X (some (none)), 1, X (none), X (some (some (none))), X (some (some (some (some (none)))))]
noncomputable def R1 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![X (none) - (X (some (some (some (some (none)))))), X (some (none)) * X (some (some (some (some (none))))) - (X (some (some (none)))), 0, X (some (none)) + (X (some (some (none)))) - (1), X (none) * X (some (none)) - (X (none)) - (X (some (none)) * X (some (some (some (none))))) + (1)]

noncomputable def reductions1 (j : Fin 5) : FactorReduction U1 (E1 j) (R1 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring

noncomputable def nextE1 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![0, X (none) * X (some (some (some (none)))) - (X (some (none))), 0, X (none) + (X (some (none))) - (1), -(X (none) * X (some (some (none)))) + (X (none) * X (some (some (some (none))))) - (X (some (some (some (none))))) + (1)]
noncomputable def nextU1 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (none), 1, X (some (some (some (none)))), X (some (none)), X (some (some (some (none))))]

noncomputable def step1 : LinearStep (Option (Option (Option (Option (Fin 0))))) 5 5 where
  sourceE := R1
  sourceU := U1
  targetE := nextE1
  targetU := nextU1
  a := 1
  b := -(X (some (some (some (none)))))
  pivot := 0
  pivot_identity := by simp [R1]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 0, 0, 0, 1]
  equation_quotient := ![1, 0, 0, 0, X (some (none)) - (1)]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring
  unit_power := ![0, 0, 1, 0, 0]
  unit_quotient := ![0, 0, 1, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring

noncomputable def E2 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![0, X (none) * X (some (some (some (none)))) - (X (some (none))), 0, X (none) + (X (some (none))) - (1), -(X (none) * X (some (some (none)))) + (X (none) * X (some (some (some (none))))) - (X (some (some (some (none))))) + (1)]
noncomputable def U2 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (none), 1, X (some (some (some (none)))), X (some (none)), X (some (some (some (none))))]
noncomputable def R2 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![0, X (none) * X (some (some (some (none)))) - (X (some (none))), 0, X (none) + (X (some (none))) - (1), -(X (none) * X (some (some (none)))) + (X (none) * X (some (some (some (none))))) - (X (some (some (some (none))))) + (1)]

noncomputable def reductions2 (j : Fin 5) : FactorReduction U2 (E2 j) (R2 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring

noncomputable def nextE2 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![0, -(X (none) * X (some (some (none)))) - (X (none)) + (X (some (some (none)))), 0, 0, X (none) * X (some (none)) - (X (none) * X (some (some (none)))) - (X (some (none))) + (1)]
noncomputable def nextU2 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![-(X (none)) + (1), 1, X (some (some (none))), X (none), X (some (some (none)))]

noncomputable def step2 : LinearStep (Option (Option (Option (Fin 0)))) 5 5 where
  sourceE := R2
  sourceU := U2
  targetE := nextE2
  targetU := nextU2
  a := 1
  b := X (none) - (1)
  pivot := 3
  pivot_identity := by simp [R2]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 1, 0, 1, 1]
  equation_quotient := ![0, X (some (some (some (none)))), 0, 1, -(X (some (some (none)))) + (X (some (some (some (none)))))]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring
  unit_power := ![1, 0, 0, 0, 0]
  unit_quotient := ![1, 0, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring

noncomputable def E3 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![0, -(X (none) * X (some (some (none)))) - (X (none)) + (X (some (some (none)))), 0, 0, X (none) * X (some (none)) - (X (none) * X (some (some (none)))) - (X (some (none))) + (1)]
noncomputable def U3 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![-(X (none)) + (1), 1, X (some (some (none))), X (none), X (some (some (none)))]
noncomputable def R3 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![0, X (none) * X (some (some (none))) + (X (none)) - (X (some (some (none)))), 0, 0, -(X (none) * X (some (none))) + (X (none) * X (some (some (none)))) + (X (some (none))) - (1)]

noncomputable def reductions3 (j : Fin 5) : FactorReduction U3 (E3 j) (R3 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring

noncomputable def nextE3 : Fin 5 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, 0, 0, 0, X (none) + ((X (some (none))) ^ 2) - (X (some (none))) - (1)]
noncomputable def nextU3 : Fin 5 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![1, 1, X (some (none)), X (some (none)), X (some (none))]

noncomputable def step3 : LinearStep (Option (Option (Fin 0))) 5 5 where
  sourceE := R3
  sourceU := U3
  targetE := nextE3
  targetU := nextU3
  a := X (some (none)) + (1)
  b := -(X (some (none)))
  pivot := 1
  pivot_identity := by simp [R3]<;> ring
  coefficient_or_constant_unit := Sum.inr {
      count := 1
      selected := ![2]
      quotient := -(1)
      identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 1, 0, 0, 1]
  equation_quotient := ![0, X (some (some (none))) + (1), 0, 0, -(X (some (none))) + (X (some (some (none))))]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R3, U3, nextE3, nextU3, map_ofNat] <;> ring
  unit_power := ![1, 0, 0, 1, 0]
  unit_quotient := ![-(1), 0, 0, 1, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R3, U3, nextE3, nextU3, map_ofNat] <;> ring

noncomputable def E4 : Fin 5 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, 0, 0, 0, X (none) + ((X (some (none))) ^ 2) - (X (some (none))) - (1)]
noncomputable def U4 : Fin 5 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![1, 1, X (some (none)), X (some (none)), X (some (none))]
noncomputable def R4 : Fin 5 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, 0, 0, 0, X (none) + ((X (some (none))) ^ 2) - (X (some (none))) - (1)]

noncomputable def reductions4 (j : Fin 5) : FactorReduction U4 (E4 j) (R4 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring

noncomputable def nextE4 : Fin 5 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0, 0]
noncomputable def nextU4 : Fin 5 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![1, 1, X (none), X (none), X (none)]

noncomputable def step4 : LinearStep (Option (Fin 0)) 5 5 where
  sourceE := R4
  sourceU := U4
  targetE := nextE4
  targetU := nextU4
  a := 1
  b := (X (none)) ^ 2 - (X (none)) - (1)
  pivot := 4
  pivot_identity := by simp [R4]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 0, 0, 0, 1]
  equation_quotient := ![0, 0, 0, 0, 1]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R4, U4, nextE4, nextU4, map_ofNat] <;> ring
  unit_power := ![0, 0, 0, 0, 0]
  unit_quotient := ![0, 0, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R4, U4, nextE4, nextU4, map_ofNat] <;> ring

noncomputable def E5 : Fin 5 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0, 0]
noncomputable def U5 : Fin 5 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![1, 1, X (none), X (none), X (none)]
noncomputable def R5 : Fin 5 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0, 0]

noncomputable def reductions5 (j : Fin 5) : FactorReduction U5 (E5 j) (R5 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U5, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E5, R5]<;> ring
    · simp [E5, R5]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U5, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E5, R5]<;> ring
    · simp [E5, R5]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U5, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E5, R5]<;> ring
    · simp [E5, R5]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U5, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E5, R5]<;> ring
    · simp [E5, R5]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U5, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E5, R5]<;> ring
    · simp [E5, R5]<;> ring

theorem dense5 : RationallyDenseSystem E5 U5 := by
  apply dense_system_of_factor_reductions E5 R5 U5 reductions5
  apply zero_equations_system_dense R5 U5
  intro j; fin_cases j <;> rfl

theorem dense4 : RationallyDenseSystem E4 U4 := by
  apply dense_system_of_factor_reductions E4 R4 U4 reductions4
  exact step4.preserves_density dense5

theorem dense3 : RationallyDenseSystem E3 U3 := by
  apply dense_system_of_factor_reductions E3 R3 U3 reductions3
  exact step3.preserves_density dense4

theorem dense2 : RationallyDenseSystem E2 U2 := by
  apply dense_system_of_factor_reductions E2 R2 U2 reductions2
  exact step2.preserves_density dense3

theorem dense1 : RationallyDenseSystem E1 U1 := by
  apply dense_system_of_factor_reductions E1 R1 U1 reductions1
  exact step1.preserves_density dense2

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  exact step0.preserves_density dense1

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart563Omit5
end

/- Source: ChartTables/Case563Omit5.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart563Omit5
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Option (Option (Option (Option (Fin 0))))))) :=
  ![![.one, .one, .one, .variable (some (some (some (some (none)))))], ![.one, .zero, .variable (some (some (none))), .one], ![.one, .variable (none), .zero, .variable (some (none))], ![.zero, .one, .variable (some (some (some (none)))), .variable (some (some (some (some (some (none))))))]]

noncomputable def chartPositions : (Option (Option (Option (Option (Option (Option (Fin 0))))))) → Coordinate × Coordinate :=
  Option.elim' (2, 1) (Option.elim' (2, 3) (Option.elim' (1, 2) (Option.elim' (3, 2) (Option.elim' (0, 3) (Option.elim' (3, 3) ![])))))

noncomputable def chartUnitVariables : Fin 5 → (Option (Option (Option (Option (Option (Option (Fin 0))))))) :=
  ![some (some (none)), none, some (none), some (some (some (none))), some (some (some (some (some (none)))))]

noncomputable def chartLabelCode : ℕ := 16434824

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, false, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, false, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, false, false, false, false, false, true, false, false, false, false, false, true, false, false, true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Option (Option (Option (Option (Fin 0))))))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 563)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 563) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨13, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70)
      rw [minorFormula_at_13]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨24, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (24 : Fin 70)
      rw [minorFormula_at_24]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨45, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70)
      rw [minorFormula_at_45]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨61, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70)
      rw [minorFormula_at_61]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨67, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (67 : Fin 70)
      rw [minorFormula_at_67]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (1 : Fin 70) = _
      rw [minorFormula_at_1]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (7 : Fin 70) = _
      rw [minorFormula_at_7]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70)
      rw [minorFormula_at_13]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (16 : Fin 70) = _
      rw [minorFormula_at_16]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨1, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (24 : Fin 70)
      rw [minorFormula_at_24]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨2, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70)
      rw [minorFormula_at_45]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨3, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70)
      rw [minorFormula_at_61]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨4, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (67 : Fin 70)
      rw [minorFormula_at_67]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(4,1),(4,2),(5,3),(1,7)]

theorem chart_schedule : Papers.MatrixGaugeNormalization.checkSchedule chartForestRoots chartForestSteps = true := by
  decide +kernel

theorem chart_steps_are_ones : ∀ e ∈ chartForestSteps,
    (∃ i j : Coordinate, e = (firstFour i, lastFour j) ∧ chartEntries i j = .one) ∨
    (∃ i j : Coordinate, e = (lastFour j, firstFour i) ∧ chartEntries i j = .one) := by
  decide +kernel

theorem chart_ones_are_steps : ∀ i j : Coordinate, chartEntries i j = .one →
    (firstFour i, lastFour j) ∈ chartForestSteps ∨
    (lastFour j, firstFour i) ∈ chartForestSteps := by
  decide +kernel

noncomputable def chart_certificate : ChartCertificate (Option (Option (Option (Option (Option (Option (Fin 0))))))) 5 5
    (MatroidCatalogue.N8R4.family 563) where
  entries := chartEntries
  positions := chartPositions
  unitVariables := chartUnitVariables
  labelCode := chartLabelCode
  basisMark := chartBasisMark
  requiredZero := chartRequiredZero
  polynomials := chartMinorPolynomials
  equations := E0
  units := U0
  roots := chartForestRoots
  steps := chartForestSteps
  parameters := chart_parameters
  minors := chart_minors
  pattern := chart_pattern
  first_basis := chart_first_basis
  constraints := chart_entry_constraints
  equation_table := chart_equations
  units_exact := chart_units_exact
  required_nonbasis := chart_required_nonbasis
  schedule := chart_schedule
  steps_are_ones := chart_steps_are_ones
  ones_are_steps := chart_ones_are_steps

noncomputable def omittedFourSet : Finset Point := {1,2,3,7}

theorem chart_required_except : ∀ i, chartBasisMark i ≠ true →
    minorSet i ≠ omittedFourSet → chartRequiredZero i = true := by
  decide +kernel

theorem chart_omitted_label : omittedFourSet.image
    (BasisCertificates.checkedPermutation 8 chartLabelCode chart_pattern.permutation_valid) =
    ({1,2,3,7} : Finset Point) := by
  decide +kernel

/-- The omitted nonbasis is specified using the actual catalogue labels. -/
theorem family_selected_density {n : ℕ}
    (p : Matrix Point Coordinate ℝ)
    (hp : MatroidChecked.GoldenSelectedRanks.Golden p)
    (σ : Equiv.Perm Point)
    (hcatalogue : (VectorBasisFamilies.vectorBases p).image (fun S => S.image σ) =
      MatroidCatalogue.N8R4.family 563)
    (Z : Fin n → Finset Point)
    (havoid : ∀ j, (Z j).image σ ≠ ({1,2,3,7} : Finset Point)) :
    p ∈ closure (ChirotopeDensity.SelectedRankRealizations p Z) := by
  apply MatroidChecked.GoldenSelectedRanks.ChartCertificate.selected_density_of_omission
    chart_certificate rationally_dense p hp σ hcatalogue omittedFourSet
    chart_required_except Z
  change ∀ j, (Z j).image σ ≠ omittedFourSet.image
    (BasisCertificates.checkedPermutation 8 chartLabelCode chart_pattern.permutation_valid)
  rw [chart_omitted_label]
  exact havoid

end Papers.RationalityTen.Chart563Omit5
end

/- Source: Charts/Case563Omit6.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart563Omit6
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![X (none) * X (some (some (some (some (none))))) - (X (some (none))), -(X (some (some (none))) * X (some (some (some (some (none)))))) + (X (some (some (some (none))))), -(X (some (some (none)))) - (X (some (some (some (none))))) + (1), -(X (some (none)) * X (some (some (none)))) + (X (some (none))) - (1)]
noncomputable def U0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![X (some (some (none))), X (none), X (some (none)), X (some (some (some (none)))), X (some (some (some (some (none)))))]
noncomputable def R0 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![X (none) * X (some (some (some (some (none))))) - (X (some (none))), X (some (some (none))) * X (some (some (some (some (none))))) - (X (some (some (some (none))))), X (some (some (none))) + (X (some (some (some (none))))) - (1), X (some (none)) * X (some (some (none))) - (X (some (none))) + (1)]

noncomputable def reductions0 (j : Fin 4) : FactorReduction U0 (E0 j) (R0 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring

noncomputable def nextE0 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![0, X (some (none)) * X (some (some (some (none)))) - (X (some (some (none)))), X (some (none)) + (X (some (some (none)))) - (1), X (none) * X (some (none)) - (X (none)) + (1)]
noncomputable def nextU0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (some (none)), X (none), X (none), X (some (some (none))), X (some (some (some (none))))]

noncomputable def step0 : LinearStep (Option (Option (Option (Option (Fin 0))))) 4 5 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := X (some (some (some (none))))
  b := -(X (none))
  pivot := 0
  pivot_identity := by simp [R0]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 1
      selected := ![4]
      quotient := 1
      identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 0, 0, 0]
  equation_quotient := ![X (some (some (some (some (none))))), 0, 0, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![0, 1, 0, 0, 0]
  unit_quotient := ![0, 1, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![0, X (some (none)) * X (some (some (some (none)))) - (X (some (some (none)))), X (some (none)) + (X (some (some (none)))) - (1), X (none) * X (some (none)) - (X (none)) + (1)]
noncomputable def U1 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (some (none)), X (none), X (none), X (some (some (none))), X (some (some (some (none))))]
noncomputable def R1 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![0, X (some (none)) * X (some (some (some (none)))) - (X (some (some (none)))), X (some (none)) + (X (some (some (none)))) - (1), X (none) * X (some (none)) - (X (none)) + (1)]

noncomputable def reductions1 (j : Fin 4) : FactorReduction U1 (E1 j) (R1 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring

noncomputable def nextE1 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![0, X (none) * X (some (some (none))) - (X (some (none))), X (none) + (X (some (none))) - (1), 0]
noncomputable def nextU1 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none), -(1), -(1), X (some (none)), X (some (some (none)))]

noncomputable def step1 : LinearStep (Option (Option (Option (Fin 0)))) 4 5 where
  sourceE := R1
  sourceU := U1
  targetE := nextE1
  targetU := nextU1
  a := X (none) - (1)
  b := 1
  pivot := 3
  pivot_identity := by simp [R1]<;> ring
  coefficient_or_constant_unit := Sum.inr {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 0, 0, 1]
  equation_quotient := ![0, 0, 0, X (some (none)) - (1)]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring
  unit_power := ![0, 1, 1, 0, 0]
  unit_quotient := ![0, 1, 1, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring

noncomputable def E2 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![0, X (none) * X (some (some (none))) - (X (some (none))), X (none) + (X (some (none))) - (1), 0]
noncomputable def U2 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none), -(1), -(1), X (some (none)), X (some (some (none)))]
noncomputable def R2 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![0, X (none) * X (some (some (none))) - (X (some (none))), X (none) + (X (some (none))) - (1), 0]

noncomputable def reductions2 (j : Fin 4) : FactorReduction U2 (E2 j) (R2 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring

noncomputable def nextE2 : Fin 4 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, -(X (none) * X (some (none))) - (X (none)) + (X (some (none))), 0, 0]
noncomputable def nextU2 : Fin 5 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![-(X (none)) + (1), -(1), -(1), X (none), X (some (none))]

noncomputable def step2 : LinearStep (Option (Option (Fin 0))) 4 5 where
  sourceE := R2
  sourceU := U2
  targetE := nextE2
  targetU := nextU2
  a := 1
  b := X (none) - (1)
  pivot := 2
  pivot_identity := by simp [R2]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 1, 1, 0]
  equation_quotient := ![0, X (some (some (none))), 1, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring
  unit_power := ![1, 0, 0, 0, 0]
  unit_quotient := ![1, 0, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring

noncomputable def E3 : Fin 4 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, -(X (none) * X (some (none))) - (X (none)) + (X (some (none))), 0, 0]
noncomputable def U3 : Fin 5 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![-(X (none)) + (1), -(1), -(1), X (none), X (some (none))]
noncomputable def R3 : Fin 4 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, X (none) * X (some (none)) + (X (none)) - (X (some (none))), 0, 0]

noncomputable def reductions3 (j : Fin 4) : FactorReduction U3 (E3 j) (R3 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring

noncomputable def nextE3 : Fin 4 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0]
noncomputable def nextU3 : Fin 5 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![1, -(1), -(1), X (none), X (none)]

noncomputable def step3 : LinearStep (Option (Fin 0)) 4 5 where
  sourceE := R3
  sourceU := U3
  targetE := nextE3
  targetU := nextU3
  a := X (none) + (1)
  b := -(X (none))
  pivot := 1
  pivot_identity := by simp [R3]<;> ring
  coefficient_or_constant_unit := Sum.inr {
      count := 1
      selected := ![4]
      quotient := -(1)
      identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 1, 0, 0]
  equation_quotient := ![0, X (some (none)) + (1), 0, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R3, U3, nextE3, nextU3, map_ofNat] <;> ring
  unit_power := ![1, 0, 0, 1, 0]
  unit_quotient := ![-(1), 0, 0, 1, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R3, U3, nextE3, nextU3, map_ofNat] <;> ring

noncomputable def E4 : Fin 4 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0]
noncomputable def U4 : Fin 5 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![1, -(1), -(1), X (none), X (none)]
noncomputable def R4 : Fin 4 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0]

noncomputable def reductions4 (j : Fin 4) : FactorReduction U4 (E4 j) (R4 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring

theorem dense4 : RationallyDenseSystem E4 U4 := by
  apply dense_system_of_factor_reductions E4 R4 U4 reductions4
  apply zero_equations_system_dense R4 U4
  intro j; fin_cases j <;> rfl

theorem dense3 : RationallyDenseSystem E3 U3 := by
  apply dense_system_of_factor_reductions E3 R3 U3 reductions3
  exact step3.preserves_density dense4

theorem dense2 : RationallyDenseSystem E2 U2 := by
  apply dense_system_of_factor_reductions E2 R2 U2 reductions2
  exact step2.preserves_density dense3

theorem dense1 : RationallyDenseSystem E1 U1 := by
  apply dense_system_of_factor_reductions E1 R1 U1 reductions1
  exact step1.preserves_density dense2

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  exact step0.preserves_density dense1

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart563Omit6
end

/- Source: ChartTables/Case563Omit6.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart563Omit6
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Option (Option (Option (Fin 0)))))) :=
  ![![.one, .one, .one, .zero], ![.one, .zero, .variable (some (some (none))), .one], ![.one, .variable (none), .zero, .variable (some (none))], ![.zero, .one, .variable (some (some (some (none)))), .variable (some (some (some (some (none)))))]]

noncomputable def chartPositions : (Option (Option (Option (Option (Option (Fin 0)))))) → Coordinate × Coordinate :=
  Option.elim' (2, 1) (Option.elim' (2, 3) (Option.elim' (1, 2) (Option.elim' (3, 2) (Option.elim' (3, 3) ![]))))

noncomputable def chartUnitVariables : Fin 5 → (Option (Option (Option (Option (Option (Fin 0)))))) :=
  ![some (some (none)), none, some (none), some (some (some (none))), some (some (some (some (none))))]

noncomputable def chartLabelCode : ℕ := 16434824

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, false, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, false, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, false, false, false, false, false, true, false, false, false, false, false, true, false, false, true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 563)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 563) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨13, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70)
      rw [minorFormula_at_13]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨24, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (24 : Fin 70)
      rw [minorFormula_at_24]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨61, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70)
      rw [minorFormula_at_61]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨67, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (67 : Fin 70)
      rw [minorFormula_at_67]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (1 : Fin 70) = _
      rw [minorFormula_at_1]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (7 : Fin 70) = _
      rw [minorFormula_at_7]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70)
      rw [minorFormula_at_13]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (16 : Fin 70) = _
      rw [minorFormula_at_16]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨1, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (24 : Fin 70)
      rw [minorFormula_at_24]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (38 : Fin 70) = _
      rw [minorFormula_at_38]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨2, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70)
      rw [minorFormula_at_61]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨3, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (67 : Fin 70)
      rw [minorFormula_at_67]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(4,1),(4,2),(5,3),(1,7)]

theorem chart_schedule : Papers.MatrixGaugeNormalization.checkSchedule chartForestRoots chartForestSteps = true := by
  decide +kernel

theorem chart_steps_are_ones : ∀ e ∈ chartForestSteps,
    (∃ i j : Coordinate, e = (firstFour i, lastFour j) ∧ chartEntries i j = .one) ∨
    (∃ i j : Coordinate, e = (lastFour j, firstFour i) ∧ chartEntries i j = .one) := by
  decide +kernel

theorem chart_ones_are_steps : ∀ i j : Coordinate, chartEntries i j = .one →
    (firstFour i, lastFour j) ∈ chartForestSteps ∨
    (lastFour j, firstFour i) ∈ chartForestSteps := by
  decide +kernel

noncomputable def chart_certificate : ChartCertificate (Option (Option (Option (Option (Option (Fin 0)))))) 4 5
    (MatroidCatalogue.N8R4.family 563) where
  entries := chartEntries
  positions := chartPositions
  unitVariables := chartUnitVariables
  labelCode := chartLabelCode
  basisMark := chartBasisMark
  requiredZero := chartRequiredZero
  polynomials := chartMinorPolynomials
  equations := E0
  units := U0
  roots := chartForestRoots
  steps := chartForestSteps
  parameters := chart_parameters
  minors := chart_minors
  pattern := chart_pattern
  first_basis := chart_first_basis
  constraints := chart_entry_constraints
  equation_table := chart_equations
  units_exact := chart_units_exact
  required_nonbasis := chart_required_nonbasis
  schedule := chart_schedule
  steps_are_ones := chart_steps_are_ones
  ones_are_steps := chart_ones_are_steps

noncomputable def omittedFourSet : Finset Point := {1,3,4,5}

theorem chart_required_except : ∀ i, chartBasisMark i ≠ true →
    minorSet i ≠ omittedFourSet → chartRequiredZero i = true := by
  decide +kernel

theorem chart_omitted_label : omittedFourSet.image
    (BasisCertificates.checkedPermutation 8 chartLabelCode chart_pattern.permutation_valid) =
    ({1,3,4,5} : Finset Point) := by
  decide +kernel

/-- The omitted nonbasis is specified using the actual catalogue labels. -/
theorem family_selected_density {n : ℕ}
    (p : Matrix Point Coordinate ℝ)
    (hp : MatroidChecked.GoldenSelectedRanks.Golden p)
    (σ : Equiv.Perm Point)
    (hcatalogue : (VectorBasisFamilies.vectorBases p).image (fun S => S.image σ) =
      MatroidCatalogue.N8R4.family 563)
    (Z : Fin n → Finset Point)
    (havoid : ∀ j, (Z j).image σ ≠ ({1,3,4,5} : Finset Point)) :
    p ∈ closure (ChirotopeDensity.SelectedRankRealizations p Z) := by
  apply MatroidChecked.GoldenSelectedRanks.ChartCertificate.selected_density_of_omission
    chart_certificate rationally_dense p hp σ hcatalogue omittedFourSet
    chart_required_except Z
  change ∀ j, (Z j).image σ ≠ omittedFourSet.image
    (BasisCertificates.checkedPermutation 8 chartLabelCode chart_pattern.permutation_valid)
  rw [chart_omitted_label]
  exact havoid

end Papers.RationalityTen.Chart563Omit6
end

/- Source: Charts/Case563Omit7.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart563Omit7
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![X (none) * X (some (some (some (some (none))))) - (X (some (none))), -(X (some (some (none))) * X (some (some (some (some (none)))))) + (X (some (some (some (none))))), -(X (none)) + (1), -(X (some (none)) * X (some (some (none)))) + (X (some (none))) - (1)]
noncomputable def U0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![X (some (some (none))), X (none), X (some (none)), X (some (some (some (none)))), X (some (some (some (some (none)))))]
noncomputable def R0 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![X (none) * X (some (some (some (some (none))))) - (X (some (none))), X (some (some (none))) * X (some (some (some (some (none))))) - (X (some (some (some (none))))), X (none) - (1), X (some (none)) * X (some (some (none))) - (X (some (none))) + (1)]

noncomputable def reductions0 (j : Fin 4) : FactorReduction U0 (E0 j) (R0 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring

noncomputable def nextE0 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![-(X (none)) + (X (some (some (some (none))))), X (some (none)) * X (some (some (some (none)))) - (X (some (some (none)))), 0, X (none) * X (some (none)) - (X (none)) + (1)]
noncomputable def nextU0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (some (none)), 1, X (none), X (some (some (none))), X (some (some (some (none))))]

noncomputable def step0 : LinearStep (Option (Option (Option (Option (Fin 0))))) 4 5 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := 1
  b := -(1)
  pivot := 2
  pivot_identity := by simp [R0]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 0, 1, 0]
  equation_quotient := ![X (some (some (some (some (none))))), 0, 1, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![0, 1, 0, 0, 0]
  unit_quotient := ![0, 1, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![-(X (none)) + (X (some (some (some (none))))), X (some (none)) * X (some (some (some (none)))) - (X (some (some (none)))), 0, X (none) * X (some (none)) - (X (none)) + (1)]
noncomputable def U1 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (some (none)), 1, X (none), X (some (some (none))), X (some (some (some (none))))]
noncomputable def R1 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (none) - (X (some (some (some (none))))), X (some (none)) * X (some (some (some (none)))) - (X (some (some (none)))), 0, X (none) * X (some (none)) - (X (none)) + (1)]

noncomputable def reductions1 (j : Fin 4) : FactorReduction U1 (E1 j) (R1 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring

noncomputable def nextE1 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![0, X (none) * X (some (some (none))) - (X (some (none))), 0, X (none) * X (some (some (none))) - (X (some (some (none)))) + (1)]
noncomputable def nextU1 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none), 1, X (some (some (none))), X (some (none)), X (some (some (none)))]

noncomputable def step1 : LinearStep (Option (Option (Option (Fin 0)))) 4 5 where
  sourceE := R1
  sourceU := U1
  targetE := nextE1
  targetU := nextU1
  a := 1
  b := -(X (some (some (none))))
  pivot := 0
  pivot_identity := by simp [R1]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 0, 0, 1]
  equation_quotient := ![1, 0, 0, X (some (none)) - (1)]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring
  unit_power := ![0, 0, 1, 0, 0]
  unit_quotient := ![0, 0, 1, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring

noncomputable def E2 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![0, X (none) * X (some (some (none))) - (X (some (none))), 0, X (none) * X (some (some (none))) - (X (some (some (none)))) + (1)]
noncomputable def U2 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none), 1, X (some (some (none))), X (some (none)), X (some (some (none)))]
noncomputable def R2 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![0, X (none) * X (some (some (none))) - (X (some (none))), 0, X (none) * X (some (some (none))) - (X (some (some (none)))) + (1)]

noncomputable def reductions2 (j : Fin 4) : FactorReduction U2 (E2 j) (R2 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring

noncomputable def nextE2 : Fin 4 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, 0, 0, X (none) * X (some (none)) - ((X (some (none))) ^ 2) + (X (some (none)))]
noncomputable def nextU2 : Fin 5 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none), 1, X (some (none)), X (none), X (some (none))]

noncomputable def step2 : LinearStep (Option (Option (Fin 0))) 4 5 where
  sourceE := R2
  sourceU := U2
  targetE := nextE2
  targetU := nextU2
  a := X (some (none))
  b := -(X (none))
  pivot := 1
  pivot_identity := by simp [R2]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 1
      selected := ![2]
      quotient := 1
      identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 1, 0, 1]
  equation_quotient := ![0, X (some (some (none))), 0, X (some (some (none)))]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring
  unit_power := ![1, 0, 0, 0, 0]
  unit_quotient := ![1, 0, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring

noncomputable def E3 : Fin 4 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, 0, 0, X (none) * X (some (none)) - ((X (some (none))) ^ 2) + (X (some (none)))]
noncomputable def U3 : Fin 5 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![X (none), 1, X (some (none)), X (none), X (some (none))]
noncomputable def R3 : Fin 4 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, 0, 0, X (none) - (X (some (none))) + (1)]

noncomputable def reductions3 (j : Fin 4) : FactorReduction U3 (E3 j) (R3 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := X (some (none))
      unit_witness := {
        count := 1
        selected := ![2]
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := X (some (none))
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring

noncomputable def nextE3 : Fin 4 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0]
noncomputable def nextU3 : Fin 5 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none) - (1), 1, X (none), X (none) - (1), X (none)]

noncomputable def step3 : LinearStep (Option (Fin 0)) 4 5 where
  sourceE := R3
  sourceU := U3
  targetE := nextE3
  targetU := nextU3
  a := 1
  b := -(X (none)) + (1)
  pivot := 3
  pivot_identity := by simp [R3]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 0, 0, 1]
  equation_quotient := ![0, 0, 0, 1]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R3, U3, nextE3, nextU3, map_ofNat] <;> ring
  unit_power := ![1, 0, 0, 1, 0]
  unit_quotient := ![1, 0, 0, 1, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R3, U3, nextE3, nextU3, map_ofNat] <;> ring

noncomputable def E4 : Fin 4 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0]
noncomputable def U4 : Fin 5 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![X (none) - (1), 1, X (none), X (none) - (1), X (none)]
noncomputable def R4 : Fin 4 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0]

noncomputable def reductions4 (j : Fin 4) : FactorReduction U4 (E4 j) (R4 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring

theorem dense4 : RationallyDenseSystem E4 U4 := by
  apply dense_system_of_factor_reductions E4 R4 U4 reductions4
  apply zero_equations_system_dense R4 U4
  intro j; fin_cases j <;> rfl

theorem dense3 : RationallyDenseSystem E3 U3 := by
  apply dense_system_of_factor_reductions E3 R3 U3 reductions3
  exact step3.preserves_density dense4

theorem dense2 : RationallyDenseSystem E2 U2 := by
  apply dense_system_of_factor_reductions E2 R2 U2 reductions2
  exact step2.preserves_density dense3

theorem dense1 : RationallyDenseSystem E1 U1 := by
  apply dense_system_of_factor_reductions E1 R1 U1 reductions1
  exact step1.preserves_density dense2

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  exact step0.preserves_density dense1

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart563Omit7
end

/- Source: ChartTables/Case563Omit7.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart563Omit7
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Option (Option (Option (Fin 0)))))) :=
  ![![.one, .one, .one, .zero], ![.one, .zero, .variable (some (some (none))), .one], ![.one, .variable (none), .zero, .variable (some (none))], ![.zero, .one, .variable (some (some (some (none)))), .variable (some (some (some (some (none)))))]]

noncomputable def chartPositions : (Option (Option (Option (Option (Option (Fin 0)))))) → Coordinate × Coordinate :=
  Option.elim' (2, 1) (Option.elim' (2, 3) (Option.elim' (1, 2) (Option.elim' (3, 2) (Option.elim' (3, 3) ![]))))

noncomputable def chartUnitVariables : Fin 5 → (Option (Option (Option (Option (Option (Fin 0)))))) :=
  ![some (some (none)), none, some (none), some (some (some (none))), some (some (some (some (none))))]

noncomputable def chartLabelCode : ℕ := 16434824

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, false, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, false, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, false, false, false, false, false, true, false, false, false, false, false, true, false, false, true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 563)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 563) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨13, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70)
      rw [minorFormula_at_13]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨24, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (24 : Fin 70)
      rw [minorFormula_at_24]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨45, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70)
      rw [minorFormula_at_45]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨67, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (67 : Fin 70)
      rw [minorFormula_at_67]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (1 : Fin 70) = _
      rw [minorFormula_at_1]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (7 : Fin 70) = _
      rw [minorFormula_at_7]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70)
      rw [minorFormula_at_13]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (16 : Fin 70) = _
      rw [minorFormula_at_16]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨1, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (24 : Fin 70)
      rw [minorFormula_at_24]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (38 : Fin 70) = _
      rw [minorFormula_at_38]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨2, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70)
      rw [minorFormula_at_45]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨3, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (67 : Fin 70)
      rw [minorFormula_at_67]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(4,1),(4,2),(5,3),(1,7)]

theorem chart_schedule : Papers.MatrixGaugeNormalization.checkSchedule chartForestRoots chartForestSteps = true := by
  decide +kernel

theorem chart_steps_are_ones : ∀ e ∈ chartForestSteps,
    (∃ i j : Coordinate, e = (firstFour i, lastFour j) ∧ chartEntries i j = .one) ∨
    (∃ i j : Coordinate, e = (lastFour j, firstFour i) ∧ chartEntries i j = .one) := by
  decide +kernel

theorem chart_ones_are_steps : ∀ i j : Coordinate, chartEntries i j = .one →
    (firstFour i, lastFour j) ∈ chartForestSteps ∨
    (lastFour j, firstFour i) ∈ chartForestSteps := by
  decide +kernel

noncomputable def chart_certificate : ChartCertificate (Option (Option (Option (Option (Option (Fin 0)))))) 4 5
    (MatroidCatalogue.N8R4.family 563) where
  entries := chartEntries
  positions := chartPositions
  unitVariables := chartUnitVariables
  labelCode := chartLabelCode
  basisMark := chartBasisMark
  requiredZero := chartRequiredZero
  polynomials := chartMinorPolynomials
  equations := E0
  units := U0
  roots := chartForestRoots
  steps := chartForestSteps
  parameters := chart_parameters
  minors := chart_minors
  pattern := chart_pattern
  first_basis := chart_first_basis
  constraints := chart_entry_constraints
  equation_table := chart_equations
  units_exact := chart_units_exact
  required_nonbasis := chart_required_nonbasis
  schedule := chart_schedule
  steps_are_ones := chart_steps_are_ones
  ones_are_steps := chart_ones_are_steps

noncomputable def omittedFourSet : Finset Point := {2,4,5,6}

theorem chart_required_except : ∀ i, chartBasisMark i ≠ true →
    minorSet i ≠ omittedFourSet → chartRequiredZero i = true := by
  decide +kernel

theorem chart_omitted_label : omittedFourSet.image
    (BasisCertificates.checkedPermutation 8 chartLabelCode chart_pattern.permutation_valid) =
    ({2,4,5,6} : Finset Point) := by
  decide +kernel

/-- The omitted nonbasis is specified using the actual catalogue labels. -/
theorem family_selected_density {n : ℕ}
    (p : Matrix Point Coordinate ℝ)
    (hp : MatroidChecked.GoldenSelectedRanks.Golden p)
    (σ : Equiv.Perm Point)
    (hcatalogue : (VectorBasisFamilies.vectorBases p).image (fun S => S.image σ) =
      MatroidCatalogue.N8R4.family 563)
    (Z : Fin n → Finset Point)
    (havoid : ∀ j, (Z j).image σ ≠ ({2,4,5,6} : Finset Point)) :
    p ∈ closure (ChirotopeDensity.SelectedRankRealizations p Z) := by
  apply MatroidChecked.GoldenSelectedRanks.ChartCertificate.selected_density_of_omission
    chart_certificate rationally_dense p hp σ hcatalogue omittedFourSet
    chart_required_except Z
  change ∀ j, (Z j).image σ ≠ omittedFourSet.image
    (BasisCertificates.checkedPermutation 8 chartLabelCode chart_pattern.permutation_valid)
  rw [chart_omitted_label]
  exact havoid

end Papers.RationalityTen.Chart563Omit7
end

/- Source: Charts/Case563Omit8.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.Chart563Omit8
open Set MvPolynomial RationalElimination MultiaffineDensity
open scoped BigOperators

/- Generated candidate certificates: all identities must be kernel checked.
   This file does not certify its own connection to a matroid. -/

noncomputable def E0 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![X (none) * X (some (some (some (some (none))))) - (X (some (none))), -(X (some (some (none))) * X (some (some (some (some (none)))))) + (X (some (some (some (none))))), -(X (none)) + (1), -(X (some (some (none)))) - (X (some (some (some (none))))) + (1)]
noncomputable def U0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![X (some (some (none))), X (none), X (some (none)), X (some (some (some (none)))), X (some (some (some (some (none)))))]
noncomputable def R0 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  ![X (none) * X (some (some (some (some (none))))) - (X (some (none))), X (some (some (none))) * X (some (some (some (some (none))))) - (X (some (some (some (none))))), X (none) - (1), X (some (some (none))) + (X (some (some (some (none))))) - (1)]

noncomputable def reductions0 (j : Fin 4) : FactorReduction U0 (E0 j) (R0 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E0, R0]<;> ring
    · simp [E0, R0]<;> ring

noncomputable def nextE0 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![-(X (none)) + (X (some (some (some (none))))), X (some (none)) * X (some (some (some (none)))) - (X (some (some (none)))), 0, X (some (none)) + (X (some (some (none)))) - (1)]
noncomputable def nextU0 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (some (none)), 1, X (none), X (some (some (none))), X (some (some (some (none))))]

noncomputable def step0 : LinearStep (Option (Option (Option (Option (Fin 0))))) 4 5 where
  sourceE := R0
  sourceU := U0
  targetE := nextE0
  targetU := nextU0
  a := 1
  b := -(1)
  pivot := 2
  pivot_identity := by simp [R0]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U0, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 0, 1, 0]
  equation_quotient := ![X (some (some (some (some (none))))), 0, 1, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring
  unit_power := ![0, 1, 0, 0, 0]
  unit_quotient := ![0, 1, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R0, U0, nextE0, nextU0, map_ofNat] <;> ring

noncomputable def E1 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![-(X (none)) + (X (some (some (some (none))))), X (some (none)) * X (some (some (some (none)))) - (X (some (some (none)))), 0, X (some (none)) + (X (some (some (none)))) - (1)]
noncomputable def U1 : Fin 5 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (some (none)), 1, X (none), X (some (some (none))), X (some (some (some (none))))]
noncomputable def R1 : Fin 4 → MvPolynomial (Option (Option (Option (Option (Fin 0))))) ℚ :=
  ![X (none) - (X (some (some (some (none))))), X (some (none)) * X (some (some (some (none)))) - (X (some (some (none)))), 0, X (some (none)) + (X (some (some (none)))) - (1)]

noncomputable def reductions1 (j : Fin 4) : FactorReduction U1 (E1 j) (R1 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E1, R1]<;> ring
    · simp [E1, R1]<;> ring

noncomputable def nextE1 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![0, X (none) * X (some (some (none))) - (X (some (none))), 0, X (none) + (X (some (none))) - (1)]
noncomputable def nextU1 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none), 1, X (some (some (none))), X (some (none)), X (some (some (none)))]

noncomputable def step1 : LinearStep (Option (Option (Option (Fin 0)))) 4 5 where
  sourceE := R1
  sourceU := U1
  targetE := nextE1
  targetU := nextU1
  a := 1
  b := -(X (some (some (none))))
  pivot := 0
  pivot_identity := by simp [R1]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U1, Fin.prod_univ_succ]<;> ring }
  equation_power := ![1, 0, 0, 0]
  equation_quotient := ![1, 0, 0, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring
  unit_power := ![0, 0, 1, 0, 0]
  unit_quotient := ![0, 0, 1, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R1, U1, nextE1, nextU1, map_ofNat] <;> ring

noncomputable def E2 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![0, X (none) * X (some (some (none))) - (X (some (none))), 0, X (none) + (X (some (none))) - (1)]
noncomputable def U2 : Fin 5 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![X (none), 1, X (some (some (none))), X (some (none)), X (some (some (none)))]
noncomputable def R2 : Fin 4 → MvPolynomial (Option (Option (Option (Fin 0)))) ℚ :=
  ![0, X (none) * X (some (some (none))) - (X (some (none))), 0, X (none) + (X (some (none))) - (1)]

noncomputable def reductions2 (j : Fin 4) : FactorReduction U2 (E2 j) (R2 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E2, R2]<;> ring
    · simp [E2, R2]<;> ring

noncomputable def nextE2 : Fin 4 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, -(X (none) * X (some (none))) - (X (none)) + (X (some (none))), 0, 0]
noncomputable def nextU2 : Fin 5 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![-(X (none)) + (1), 1, X (some (none)), X (none), X (some (none))]

noncomputable def step2 : LinearStep (Option (Option (Fin 0))) 4 5 where
  sourceE := R2
  sourceU := U2
  targetE := nextE2
  targetU := nextU2
  a := 1
  b := X (none) - (1)
  pivot := 3
  pivot_identity := by simp [R2]<;> ring
  coefficient_or_constant_unit := Sum.inl {
      count := 0
      selected := Fin.elim0
      quotient := 1
      identity := by simp [U2, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 1, 0, 1]
  equation_quotient := ![0, X (some (some (none))), 0, 1]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring
  unit_power := ![1, 0, 0, 0, 0]
  unit_quotient := ![1, 0, 0, 0, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R2, U2, nextE2, nextU2, map_ofNat] <;> ring

noncomputable def E3 : Fin 4 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, -(X (none) * X (some (none))) - (X (none)) + (X (some (none))), 0, 0]
noncomputable def U3 : Fin 5 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![-(X (none)) + (1), 1, X (some (none)), X (none), X (some (none))]
noncomputable def R3 : Fin 4 → MvPolynomial (Option (Option (Fin 0))) ℚ :=
  ![0, X (none) * X (some (none)) + (X (none)) - (X (some (none))), 0, 0]

noncomputable def reductions3 (j : Fin 4) : FactorReduction U3 (E3 j) (R3 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := -(1)
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := -(1)
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := -(1)
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E3, R3]<;> ring
    · simp [E3, R3]<;> ring

noncomputable def nextE3 : Fin 4 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0]
noncomputable def nextU3 : Fin 5 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![1, 1, X (none), X (none), X (none)]

noncomputable def step3 : LinearStep (Option (Fin 0)) 4 5 where
  sourceE := R3
  sourceU := U3
  targetE := nextE3
  targetU := nextU3
  a := X (none) + (1)
  b := -(X (none))
  pivot := 1
  pivot_identity := by simp [R3]<;> ring
  coefficient_or_constant_unit := Sum.inr {
      count := 1
      selected := ![2]
      quotient := -(1)
      identity := by simp [U3, Fin.prod_univ_succ]<;> ring }
  equation_power := ![0, 1, 0, 0]
  equation_quotient := ![0, X (some (none)) + (1), 0, 0]
  equation_identity := by
    intro j; fin_cases j <;>
      norm_num [R3, U3, nextE3, nextU3, map_ofNat] <;> ring
  unit_power := ![1, 0, 0, 1, 0]
  unit_quotient := ![-(1), 0, 0, 1, 0]
  unit_identity := by
    intro j; fin_cases j <;>
      norm_num [R3, U3, nextE3, nextU3, map_ofNat] <;> ring

noncomputable def E4 : Fin 4 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0]
noncomputable def U4 : Fin 5 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![1, 1, X (none), X (none), X (none)]
noncomputable def R4 : Fin 4 → MvPolynomial (Option (Fin 0)) ℚ :=
  ![0, 0, 0, 0]

noncomputable def reductions4 (j : Fin 4) : FactorReduction U4 (E4 j) (R4 j) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => Fin.elim0 j) j) j) j) j
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring
  · refine {
      power := 1
      power_pos := by decide
      multiplier := 1
      unit := 1
      unit_witness := {
        count := 0
        selected := Fin.elim0
        quotient := 1
        identity := by simp [U4, Fin.prod_univ_succ]<;> ring }
      forward_identity := ?_
      reverse_quotient := 1
      reverse_identity := ?_ }
    · simp [E4, R4]<;> ring
    · simp [E4, R4]<;> ring

theorem dense4 : RationallyDenseSystem E4 U4 := by
  apply dense_system_of_factor_reductions E4 R4 U4 reductions4
  apply zero_equations_system_dense R4 U4
  intro j; fin_cases j <;> rfl

theorem dense3 : RationallyDenseSystem E3 U3 := by
  apply dense_system_of_factor_reductions E3 R3 U3 reductions3
  exact step3.preserves_density dense4

theorem dense2 : RationallyDenseSystem E2 U2 := by
  apply dense_system_of_factor_reductions E2 R2 U2 reductions2
  exact step2.preserves_density dense3

theorem dense1 : RationallyDenseSystem E1 U1 := by
  apply dense_system_of_factor_reductions E1 R1 U1 reductions1
  exact step1.preserves_density dense2

theorem dense0 : RationallyDenseSystem E0 U0 := by
  apply dense_system_of_factor_reductions E0 R0 U0 reductions0
  exact step0.preserves_density dense1

/-- Rational density of the normalized polynomial system. -/
theorem rationally_dense : RationallyDenseSystem E0 U0 := dense0

end Papers.RationalityTen.Chart563Omit8
end

/- Source: ChartTables/Case563Omit8.lean. -/
section

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option synthInstance.maxSize 8192

namespace Papers.RationalityTen.Chart563Omit8
open MvPolynomial MatroidChecked.ChartPolynomial
open MatroidChecked.ChartRealization (ChartCertificate)
open BasisCertificates (Table)

/- Generated candidate data: every claimed connection below must pass Lean. -/
noncomputable def chartEntries : Coordinate → Coordinate → Entry (Option (Option (Option (Option (Option (Fin 0)))))) :=
  ![![.one, .one, .one, .zero], ![.one, .zero, .variable (some (some (none))), .one], ![.one, .variable (none), .zero, .variable (some (none))], ![.zero, .one, .variable (some (some (some (none)))), .variable (some (some (some (some (none)))))]]

noncomputable def chartPositions : (Option (Option (Option (Option (Option (Fin 0)))))) → Coordinate × Coordinate :=
  Option.elim' (2, 1) (Option.elim' (2, 3) (Option.elim' (1, 2) (Option.elim' (3, 2) (Option.elim' (3, 3) ![]))))

noncomputable def chartUnitVariables : Fin 5 → (Option (Option (Option (Option (Option (Fin 0)))))) :=
  ![some (some (none)), none, some (none), some (some (some (none))), some (some (some (some (none))))]

noncomputable def chartLabelCode : ℕ := 16434824

noncomputable def chartBasisMark : Fin 70 → Bool :=
  ![true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, false, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, false, true, true]

noncomputable def chartRequiredZero : Fin 70 → Bool :=
  ![false, true, false, false, false, false, false, true, false, false, false, false, false, true, false, false, true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false]

noncomputable def chartMinorPolynomials : Fin 70 → MvPolynomial (Option (Option (Option (Option (Option (Fin 0)))))) ℚ :=
  actualMinor chartEntries

theorem chart_parameters : ParameterCertificate chartEntries chartPositions := by
  constructor <;> decide +kernel

theorem chart_units_exact : ∀ j, U0 j = X (chartUnitVariables j) := by
  intro j; fin_cases j <;> rfl

theorem chart_minors : MinorTableCertificate chartEntries chartMinorPolynomials := by
  exact ⟨fun _ => rfl⟩

theorem chart_pattern : PatternCertificate (MatroidCatalogue.N8R4.family 563)
    chartLabelCode chartBasisMark := by
  constructor <;> decide +kernel

theorem chart_first_basis : chartBasisMark 0 = true := by decide +kernel

theorem chart_required_nonbasis : ∀ i, chartRequiredZero i = true → chartBasisMark i ≠ true := by
  decide +kernel

theorem chart_entry_constraints : EntryConstraintCertificate
    (MatroidCatalogue.N8R4.family 563) chartLabelCode chartEntries
    chartPositions chartUnitVariables := by
  constructor <;> decide +kernel

theorem chart_equations : EquationTableCertificate
    chartRequiredZero chartMinorPolynomials E0 := by
  constructor
  · intro j
    fin_cases j
    · refine ⟨13, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70)
      rw [minorFormula_at_13]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨24, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (24 : Fin 70)
      rw [minorFormula_at_24]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨45, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70)
      rw [minorFormula_at_45]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · refine ⟨61, by decide +kernel, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70)
      rw [minorFormula_at_61]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
  · intro i hi
    fin_cases i
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (1 : Fin 70) = _
      rw [minorFormula_at_1]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (7 : Fin 70) = _
      rw [minorFormula_at_7]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨0, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (13 : Fin 70)
      rw [minorFormula_at_13]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (16 : Fin 70) = _
      rw [minorFormula_at_16]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨1, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (24 : Fin 70)
      rw [minorFormula_at_24]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · apply Or.inl
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change minorFormula (fun r c => (chartEntries r c).polynomial) (38 : Fin 70) = _
      rw [minorFormula_at_38]
      dsimp [
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨2, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (45 : Fin 70)
      rw [minorFormula_at_45]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · refine Or.inr ⟨3, ?_⟩
      rw [chartMinorPolynomials, actualMinor_eq_formula]
      change _ = minorFormula (fun r c => (chartEntries r c).polynomial) (61 : Fin 70)
      rw [minorFormula_at_61]
      dsimp [E0,
        chartEntries, Entry.polynomial] <;> simp <;> ring
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi
    · simp [chartRequiredZero] at hi

noncomputable def chartForestRoots : Finset Point := {0}
noncomputable def chartForestSteps : List (Point × Point) := [(0,4),(0,5),(0,6),(4,1),(4,2),(5,3),(1,7)]

theorem chart_schedule : Papers.MatrixGaugeNormalization.checkSchedule chartForestRoots chartForestSteps = true := by
  decide +kernel

theorem chart_steps_are_ones : ∀ e ∈ chartForestSteps,
    (∃ i j : Coordinate, e = (firstFour i, lastFour j) ∧ chartEntries i j = .one) ∨
    (∃ i j : Coordinate, e = (lastFour j, firstFour i) ∧ chartEntries i j = .one) := by
  decide +kernel

theorem chart_ones_are_steps : ∀ i j : Coordinate, chartEntries i j = .one →
    (firstFour i, lastFour j) ∈ chartForestSteps ∨
    (lastFour j, firstFour i) ∈ chartForestSteps := by
  decide +kernel

noncomputable def chart_certificate : ChartCertificate (Option (Option (Option (Option (Option (Fin 0)))))) 4 5
    (MatroidCatalogue.N8R4.family 563) where
  entries := chartEntries
  positions := chartPositions
  unitVariables := chartUnitVariables
  labelCode := chartLabelCode
  basisMark := chartBasisMark
  requiredZero := chartRequiredZero
  polynomials := chartMinorPolynomials
  equations := E0
  units := U0
  roots := chartForestRoots
  steps := chartForestSteps
  parameters := chart_parameters
  minors := chart_minors
  pattern := chart_pattern
  first_basis := chart_first_basis
  constraints := chart_entry_constraints
  equation_table := chart_equations
  units_exact := chart_units_exact
  required_nonbasis := chart_required_nonbasis
  schedule := chart_schedule
  steps_are_ones := chart_steps_are_ones
  ones_are_steps := chart_ones_are_steps

noncomputable def omittedFourSet : Finset Point := {3,4,6,7}

theorem chart_required_except : ∀ i, chartBasisMark i ≠ true →
    minorSet i ≠ omittedFourSet → chartRequiredZero i = true := by
  decide +kernel

theorem chart_omitted_label : omittedFourSet.image
    (BasisCertificates.checkedPermutation 8 chartLabelCode chart_pattern.permutation_valid) =
    ({3,4,6,7} : Finset Point) := by
  decide +kernel

/-- The omitted nonbasis is specified using the actual catalogue labels. -/
theorem family_selected_density {n : ℕ}
    (p : Matrix Point Coordinate ℝ)
    (hp : MatroidChecked.GoldenSelectedRanks.Golden p)
    (σ : Equiv.Perm Point)
    (hcatalogue : (VectorBasisFamilies.vectorBases p).image (fun S => S.image σ) =
      MatroidCatalogue.N8R4.family 563)
    (Z : Fin n → Finset Point)
    (havoid : ∀ j, (Z j).image σ ≠ ({3,4,6,7} : Finset Point)) :
    p ∈ closure (ChirotopeDensity.SelectedRankRealizations p Z) := by
  apply MatroidChecked.GoldenSelectedRanks.ChartCertificate.selected_density_of_omission
    chart_certificate rationally_dense p hp σ hcatalogue omittedFourSet
    chart_required_except Z
  change ∀ j, (Z j).image σ ≠ omittedFourSet.image
    (BasisCertificates.checkedPermutation 8 chartLabelCode chart_pattern.permutation_valid)
  rw [chart_omitted_label]
  exact havoid

end Papers.RationalityTen.Chart563Omit8
end

end
end
end BundlePart6

section BundlePart7
/- Source: MatroidChecked/GoldenOmissionAssembly.lean -/




@[expose] public section
noncomputable section

/-!
# All nine omitted golden incidences

The finite list below is checked against the complete nonbasis family.
Each entry calls the density theorem for its literal determinant chart;
the matching permutation is transported to the actual selected zero sets.
-/

namespace Papers.RationalityTen.MatroidChecked.GoldenOmissionAssembly

open Matrix Set Topology
open ChirotopeDensity GoldenSelectedRanks ChartPolynomial
open VectorBasisFamilies (vectorBases)
open scoped Classical

def omissionSet : Fin 9 → Finset Point :=
  ![{0,1,2,4}, {0,1,3,6}, {0,1,5,7}, {0,2,3,5}, {0,2,6,7}, {1,2,3,7}, {1,3,4,5}, {2,4,5,6}, {3,4,6,7}]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem omissionSet_complete : ∀ S : Finset Point, S.card = 4 →
    S ∉ MatroidCatalogue.N8R4.family 563 → ∃ k : Fin 9, S = omissionSet k := by
  decide +kernel

theorem omitted_selected_density {n : ℕ}
    (p : Matrix Point Coordinate ℝ) (σ : Equiv.Perm Point)
    (hcatalogue : (vectorBases p).image (fun S => S.image σ) =
      MatroidCatalogue.N8R4.family 563)
    (omitted : Finset Point) (homitted : omitted ∈ goldenFlats p)
    (Z : Fin n → Finset Point) (havoid : ∀ j, Z j ≠ omitted) :
    p ∈ closure (SelectedRankRealizations p Z) := by
  have hp : Golden p := golden_of_catalogue p σ hcatalogue
  obtain ⟨hcard,hnot⟩ := (mem_goldenFlats p omitted).mp homitted
  have hcardimage : (omitted.image σ).card = 4 := by
    rwa [Finset.card_image_of_injective _ σ.injective]
  have hnotimage : omitted.image σ ∉ MatroidCatalogue.N8R4.family 563 := by
    intro h
    rw [← hcatalogue] at h
    obtain ⟨T,hT,hTO⟩ := Finset.mem_image.mp h
    exact hnot (Finset.image_injective σ.injective hTO ▸ hT)
  obtain ⟨k,hk⟩ := omissionSet_complete (omitted.image σ) hcardimage hnotimage
  have havoidimage : ∀ j, (Z j).image σ ≠ omissionSet k := by
    intro j h
    apply havoid j
    exact Finset.image_injective σ.injective (h.trans hk.symm)
  fin_cases k
  · exact Papers.RationalityTen.Chart563Omit0.family_selected_density
      p hp σ hcatalogue Z havoidimage
  · exact Papers.RationalityTen.Chart563Omit1.family_selected_density
      p hp σ hcatalogue Z havoidimage
  · exact Papers.RationalityTen.Chart563Omit2.family_selected_density
      p hp σ hcatalogue Z havoidimage
  · exact Papers.RationalityTen.Chart563Omit3.family_selected_density
      p hp σ hcatalogue Z havoidimage
  · exact Papers.RationalityTen.Chart563Omit4.family_selected_density
      p hp σ hcatalogue Z havoidimage
  · exact Papers.RationalityTen.Chart563Omit5.family_selected_density
      p hp σ hcatalogue Z havoidimage
  · exact Papers.RationalityTen.Chart563Omit6.family_selected_density
      p hp σ hcatalogue Z havoidimage
  · exact Papers.RationalityTen.Chart563Omit7.family_selected_density
      p hp σ hcatalogue Z havoidimage
  · exact Papers.RationalityTen.Chart563Omit8.family_selected_density
      p hp σ hcatalogue Z havoidimage

end Papers.RationalityTen.MatroidChecked.GoldenOmissionAssembly

end
end
end BundlePart7

section BundlePart8
/- Source: MatroidChecked/MatrixClassificationCore.lean -/







@[expose] public section
noncomputable section

/-!
# The exact matrix consequences of the eight-element classification

The classified configuration is an intrinsic row representation of the
given matrix. It is obtained from the span of its actual rows, so no rank,
nonzero-row, or generic-position hypothesis is added. Seven or fewer rows
and intrinsic ranks different from four use the preceding density theory.

The exceptional branch retains both the injective real frame and the exact
golden basis family. Its small independent subsets control kernel support;
its large spanning subsets control active-column support. With an omitted
four-element column zero set, the nine literal omitted-incidence charts
instead give the precise selected-rank density needed for reconstruction.
-/

namespace Papers.RationalityTen.MatroidChecked.MatrixClassificationCore

open Matrix Module Set Filter Topology
open ChirotopeDensity RankFourCatalogueDensity GoldenSelectedRanks
open ExactSelectedRanks GoldenOmissionAssembly
open scoped BigOperators Classical

/-- The complete rank-four density input. The closed assembly supplies the
exhaustively checked catalogue theorem; this intermediate interface is explicit. -/
def RankFourDensityInput : Prop :=
  ∀ p : Matrix (Fin 8) (Fin 4) ℝ, Spans p → ¬ HasGoldenMatroid p →
    p ∈ closure (ExactDensity.ExactRationalRealizations p)

def GoldenIntrinsic {n : ℕ} (C : Matrix (Fin 8) (Fin n) ℝ) : Prop :=
  ∃ (u : Matrix (Fin 8) (Fin 4) ℝ) (E : Matrix (Fin 4) (Fin n) ℝ),
    Spans u ∧ LinearIndependent ℝ E ∧ HasGoldenMatroid u ∧ reconstruct E u = C

theorem matrix_density_or_golden (hDensity : RankFourDensityInput) {n : ℕ} (C : Matrix (Fin 8) (Fin n) ℝ) :
    C ∈ closure {D : Matrix (Fin 8) (Fin n) ℝ |
      RationalCoordinates D ∧ D.rank = C.rank ∧ PreservesZeroEntries C D} ∨
      GoldenIntrinsic C := by
  by_cases hfour : C.rank = 4
  · obtain ⟨r,hr,u,E,hu,hE,hC⟩ := exists_intrinsic_linear_configuration C
    have hrank := intrinsic_rank_of_reconstruction u hu E hE
    rw [hC] at hrank
    change finrank ℝ (Submodule.span ℝ (Set.range C.row)) = r at hrank
    rw [← Matrix.rank_eq_finrank_span_row,hfour] at hrank
    have hr4 : r = 4 := hrank.symm
    subst r
    by_cases hgolden : HasGoldenMatroid u
    · exact Or.inr ⟨u,E,hu,hE,hgolden,hC⟩
    · apply Or.inl
      have hselected := selected_density_of_exact_density u hu
        (reconstructionZeroSet (reconstruct E u))
        (hDensity u hu hgolden)
      have hdense := zero_pattern_rank_density_from_selected_ranks u hu E hE hselected
      have hCm : Matrix.of (reconstruct E u) = C := hC
      change (Matrix.of (reconstruct E u)) ∈ closure
        {D : Matrix (Fin 8) (Fin n) ℝ | RationalCoordinates D ∧
          D.rank = (Matrix.of (reconstruct E u)).rank ∧
          PreservesZeroEntries (Matrix.of (reconstruct E u)) D} at hdense
      simpa only [hCm] using hdense
  · exact Or.inl (rational_matrix_zero_pattern_rank_density_eight_nonfour
      (by decide) C hfour)

theorem reconstruct_eq_matrix_mul {c r n : ℕ}
    (E : Matrix (Fin r) (Fin n) ℝ) (u : Matrix (Fin c) (Fin r) ℝ) :
    reconstruct E u = u * E := by
  ext i j
  simp [reconstruct,frameMap,Matrix.mul_apply,Finset.sum_apply,smul_eq_mul]

theorem frameMap_eq_transpose_mulVec {r n : ℕ}
    (E : Matrix (Fin r) (Fin n) ℝ) (a : Fin r → ℝ) :
    frameMap E a = E.transpose.mulVec a := by
  ext j
  simp [frameMap,Matrix.mulVec,dotProduct,Finset.sum_apply,smul_eq_mul,mul_comm]

theorem reconstruct_transpose_kernel {c r n : ℕ}
    (E : Matrix (Fin r) (Fin n) ℝ) (hE : LinearIndependent ℝ E)
    (u : Matrix (Fin c) (Fin r) ℝ) (v : Fin c → ℝ)
    (hker : (Matrix.of (reconstruct E u)).transpose.mulVec v = 0) :
    u.transpose.mulVec v = 0 := by
  apply frameMap_injective hE
  rw [map_zero,frameMap_eq_transpose_mulVec,Matrix.mulVec_mulVec,
    ← Matrix.transpose_mul,← reconstruct_eq_matrix_mul]
  exact hker

theorem GoldenIntrinsic.kernel_support {n : ℕ}
    {C : Matrix (Fin 8) (Fin n) ℝ} (hgolden : GoldenIntrinsic C)
    (v : Fin 8 → ℝ) (hv : v ≠ 0) (hker : C.transpose.mulVec v = 0) :
    4 ≤ (vectorSupport v).card := by
  obtain ⟨u,E,hu,hE,⟨σ,hσ⟩,hC⟩ := hgolden
  have hgu := golden_of_catalogue u σ hσ
  have hCm : Matrix.of (reconstruct E u) = C := hC
  have hkernel : u.transpose.mulVec v = 0 :=
    reconstruct_transpose_kernel E hE u v (by rw [hCm]; exact hker)
  exact exceptional_kernel_support u hgu.small_rank v hv hkernel

theorem GoldenIntrinsic.column_support {n : ℕ}
    {C : Matrix (Fin 8) (Fin n) ℝ} (hgolden : GoldenIntrinsic C) :
    ∀ j ∈ activeColumns C, 4 ≤ (columnSupport C j).card := by
  obtain ⟨u,E,hu,hE,⟨σ,hσ⟩,hC⟩ := hgolden
  have hgu := golden_of_catalogue u σ hσ
  intro j hj
  have hnonzero : C.col j ≠ 0 := by
    intro hz
    obtain ⟨i,hne⟩ := (mem_activeColumns C j).mp hj
    exact hne (congrFun hz i)
  have hcol : C.col j = (Matrix.of u).mulVec (E.col j) := by
    rw [← hC,reconstruct_eq_matrix_mul]
    rfl
  have hsupport := row_space_support_lower_bound u hgu.large_rank (E.col j)
    (fun hz => hnonzero (hcol.trans hz))
  have hcard := congrArg (fun v : Fin 8 → ℝ => (vectorSupport v).card) hcol
  change 4 ≤ (vectorSupport (C.col j)).card
  omega

theorem GoldenIntrinsic.omitted_matrix_density
    {C : Matrix (Fin 8) (Fin 9) ℝ} (hgolden : GoldenIntrinsic C)
    (homit : OmitsEveryNineFourSupportFamily C) :
    C ∈ closure {D : Matrix (Fin 8) (Fin 9) ℝ |
      RationalCoordinates D ∧ D.rank = C.rank ∧ PreservesZeroEntries C D} := by
  obtain ⟨u,E,hu,hE,⟨σ,hσ⟩,hC⟩ := hgolden
  have hgu := golden_of_catalogue u σ hσ
  obtain ⟨S,hS,havoid⟩ := homit.zeroSets rfl (goldenFlats u) hgu.flats_card
    (fun S hS => ((mem_goldenFlats u S).mp hS).1)
  have hselected := omitted_selected_density u σ hσ S hS
    (reconstructionZeroSet (reconstruct E u)) (by
      intro j
      simpa only [hC,reconstructionZeroSet,columnZeroSet] using havoid j)
  have hdense := zero_pattern_rank_density_from_selected_ranks u hu E hE hselected
  have hCm : Matrix.of (reconstruct E u) = C := hC
  change (Matrix.of (reconstruct E u)) ∈ closure
    {D : Matrix (Fin 8) (Fin 9) ℝ | RationalCoordinates D ∧
      D.rank = (Matrix.of (reconstruct E u)).rank ∧
      PreservesZeroEntries (Matrix.of (reconstruct E u)) D} at hdense
  simpa only [hCm] using hdense

/-- This is precisely the algebraic alternative consumed by the arbitrary
vertex-count, eight-relation-row geometric assembly. -/
theorem eight_row_density_or_four_column_support (hDensity : RankFourDensityInput) : EightRowMatrixDensityOrFourSupport := by
  intro c n C hc
  by_cases hseven : c ≤ 7
  · exact Or.inl (rational_matrix_zero_pattern_rank_density_seven hseven C)
  · have heq : c = 8 := by omega
    subst c
    rcases matrix_density_or_golden hDensity C with hdense | hgolden
    · exact Or.inl hdense
    · exact Or.inr hgolden.column_support

/-- The actual nine-vertex reduction gives exactly one of these two
obstruction exclusions. Neither adds an assumption to the geometric
theorem: the preceding geometry establishes the displayed disjunction. -/
theorem nine_column_exceptional_matrix_density (hDensity : RankFourDensityInput) : NineColumnExceptionalMatrixDensity := by
  intro c C hc hcase
  subst c
  rcases matrix_density_or_golden hDensity C with hdense | hgolden
  · exact hdense
  · rcases hcase with ⟨v,hv,hker,hsupport⟩ | homit
    · have hfour := hgolden.kernel_support v hv hker
      omega
    · exact hgolden.omitted_matrix_density homit

end Papers.RationalityTen.MatroidChecked.MatrixClassificationCore

end
end
end BundlePart8

module
public import Projection.Normalization.OrderedMinors
public import Projection.Normalization.MatrixNormalization
public import Projection.Topology
public import Projection.SegmentDeterminant
public import VolumePolynomials.ProjectionMixedVolumeOrder

/-!
# Bounds on actual minors from marked projection coefficients

Replace the repeated body arguments by short coordinate segments lying in its
inner ball. Monotonicity and the determinant formula for actual segment bodies
then bound each minor of the marked-vector matrix. The determinant reduction
uses a complementary coordinate frame, including the cases `k = 0` and `k = n`.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set Metric Module MeasureTheory
open scoped BigOperators Pointwise

namespace RankThreeProjection
open VolumePolynomials

/-- Renaming the finite index type along a numerical equality changes no
argument or value of the actual mixed-volume definition. -/
theorem mixedVolume_finCongr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {a b : ℕ} (h : a = b) (K : Fin a → ConvexBody E) :
    mixedVolume μ (fun i : Fin b => K ((finCongr h).symm i)) = mixedVolume μ K := by
  subst b
  rfl

/-- Dimension-matched monotonicity, also admitting the empty tuple. -/
theorem mixedVolume_mono_dimension {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {d : ℕ} (hdim : finrank ℝ E = d) (K L : Fin d → ConvexBody E)
    (hKL : ∀ i, K i ≤ L i) : mixedVolume μ K ≤ mixedVolume μ L := by
  cases d with
  | zero =>
    have h : K = L := funext fun i => Fin.elim0 i
    rw [h]
  | succ d => exact mixedVolume_mono_all μ hdim K L hKL

theorem centeredSegment_subset_closedBall {n : ℕ} {ρ : ℝ} (v : Space n)
    (hv : ‖v‖ ≤ ρ) : (centeredSegment v : Set (Space n)) ⊆ closedBall 0 ρ := by
  apply (convex_closedBall (0 : Space n) ρ).segment_subset
  · apply mem_closedBall_zero_iff.mpr
    rw [norm_smul]
    norm_num only [Real.norm_eq_abs, abs_neg, abs_div, abs_one]
    exact (mul_le_of_le_one_left (norm_nonneg v) (by norm_num : (1 / 2 : ℝ) ≤ 1)).trans hv
  · apply mem_closedBall_zero_iff.mpr
    rw [norm_smul]
    norm_num only [Real.norm_eq_abs, abs_div, abs_one]
    exact (mul_le_of_le_one_left (norm_nonneg v) (by norm_num : (1 / 2 : ℝ) ≤ 1)).trans hv

/-- Completing the rows of a minor by the complementary coordinate vectors
turns its determinant into the volume of an actual tuple of `n` segments. -/
theorem complete_minor_by_coordinate_segments {n k : ℕ} (hkn : k ≤ n)
    (U : Fin n → Space n) (rows cols : Fin k → Fin n) (hrows : Function.Injective rows)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∃ W : Fin (n - k + k) → Space n,
      (∀ i : Fin (n - k), ‖W (Fin.castAdd k i)‖ ≤ ρ) ∧
      (∀ i : Fin k, W (Fin.natAdd (n - k) i) = U (cols i)) ∧
      (n.factorial : ℝ) * mixedVolume volume (fun i => centeredSegment (W i)) =
        ρ ^ (n - k) * |((columnsMatrix U).submatrix rows cols).det| := by
  classical
  let τ := {i : Fin n // i ∉ Set.range rows}
  let e₀ : Fin k ⊕ τ ≃ Fin n := ProjectionVolumes.selectionEquiv rows hrows
  have hcard : Fintype.card τ = n - k := by
    have h := Fintype.card_congr e₀
    simp only [Fintype.card_sum, Fintype.card_fin] at h
    omega
  let et : Fin (n - k) ≃ τ := Fintype.equivOfCardEq (by simp only [Fintype.card_fin, hcard])
  let er : Fin (n - k) ⊕ Fin k ≃ Fin n :=
    ((Equiv.sumCongr et (Equiv.refl (Fin k))).trans (Equiv.sumComm τ (Fin k))).trans e₀
  have her₁ (i : Fin (n - k)) : er (Sum.inl i) = (et i).val := rfl
  have her₂ (i : Fin k) : er (Sum.inr i) = rows i := rfl
  have hsum : n - k + k = n := Nat.sub_add_cancel hkn
  let ec : Fin (n - k) ⊕ Fin k ≃ Fin n := finSumFinEquiv.trans (finCongr hsum)
  let W : Fin (n - k + k) → Space n :=
    Fin.append (fun i : Fin (n - k) => ρ • Pi.single (et i).val 1)
      (fun i : Fin k => U (cols i))
  let V : Fin n → Space n := fun i => W ((finCongr hsum).symm i)
  have hV₁ (i : Fin (n - k)) : V (ec (Sum.inl i)) = ρ • Pi.single (et i).val 1 := by
    simp only [V, ec, Equiv.trans_apply, Equiv.symm_apply_apply,
      finSumFinEquiv_apply_left, W, Fin.append_left]
  have hV₂ (i : Fin k) : V (ec (Sum.inr i)) = U (cols i) := by
    simp only [V, ec, Equiv.trans_apply, Equiv.symm_apply_apply,
      finSumFinEquiv_apply_right, W, Fin.append_right]
  let B := (columnsMatrix U).submatrix rows cols
  let A : Matrix (Fin (n - k)) (Fin k) ℝ := fun i j => U (cols j) (et i).val
  have hblock : (columnsMatrix V).submatrix er ec =
      Matrix.fromBlocks (Matrix.diagonal (fun _ : Fin (n - k) => ρ)) A 0 B := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        simp only [Matrix.submatrix_apply, columnsMatrix, hV₁, her₁,
          Matrix.fromBlocks_apply₁₁]
        by_cases hij : i = j
        · subst j
          simp [Matrix.diagonal_apply]
        · have hne : (et i).val ≠ (et j).val := fun h => hij (et.injective (Subtype.ext h))
          simp [Pi.single_apply, Matrix.diagonal_apply, hij, Ne.symm hij, hne, Ne.symm hne]
      | inr j =>
        simp only [Matrix.submatrix_apply, columnsMatrix, hV₂, her₁,
          Matrix.fromBlocks_apply₁₂, A]
        rfl
    | inr i =>
      cases j with
      | inl j =>
        simp only [Matrix.submatrix_apply, columnsMatrix, hV₁, her₂,
          Matrix.fromBlocks_apply₂₁]
        have hne : rows i ≠ (et j).val := fun h => (et j).property ⟨i, h⟩
        simp [Pi.single_apply, hne, Ne.symm hne]
      | inr j =>
        simp only [Matrix.submatrix_apply, columnsMatrix, hV₂, her₂,
          Matrix.fromBlocks_apply₂₂, B]
  have hdet : |(columnsMatrix V).det| = ρ ^ (n - k) * |B.det| := by
    rw [← Matrix.abs_det_submatrix_equiv_equiv er ec (columnsMatrix V), hblock,
      Matrix.det_fromBlocks_zero₂₁, Matrix.det_diagonal, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, abs_mul, abs_of_nonneg (pow_nonneg hρ _)]
  refine ⟨W, ?_, ?_, ?_⟩
  · intro i
    simpa only [W, Fin.append_left, norm_smul, Pi.norm_single, norm_one, mul_one,
      Real.norm_of_nonneg hρ] using (le_rfl : ρ ≤ ρ)
  · intro i
    exact Fin.append_right _ _ i
  · have hcast := mixedVolume_finCongr volume hsum (fun i => centeredSegment (W i))
    rw [← hcast, mixedVolume_centered_segments, hdet]

/-- A selected minor is bounded by its actual marked coefficient. No spanning
or invertibility condition is required on the marked vectors. -/
theorem ordered_minor_bound {n k : ℕ} (hkn : k ≤ n)
    (K : Body n) (U : Fin n → Space n) (I J : Deleted n k)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hinner : closedBall 0 ρ ⊆ (K : Set (Space n))) :
    ρ ^ (n - k) *
        |((columnsMatrix U).submatrix (J.val.orderEmbOfFin J.property)
          (I.val.orderEmbOfFin I.property)).det| ≤
      ((n - k).factorial : ℝ) * allMarkedArray K U I := by
  obtain ⟨W, hWnorm, hWmark, hWdet⟩ := complete_minor_by_coordinate_segments hkn U
    (J.val.orderEmbOfFin J.property) (I.val.orderEmbOfFin I.property)
    (J.val.orderEmbOfFin J.property).injective ρ hρ
  have hcontain : ∀ i, centeredSegment (W i) ≤ markedTuple K U I i := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp only [markedTuple, Fin.append_left]
      apply SetLike.coe_subset_coe.mp
      exact (centeredSegment_subset_closedBall _ (hWnorm j)).trans hinner
    · intro j
      simp only [markedTuple, Fin.append_right, hWmark]
      exact le_rfl
  have hdim : finrank ℝ (Space n) = n - k + k := by
    simp only [Space, Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
      Nat.sub_add_cancel hkn]
  have hmono := mixedVolume_mono_dimension volume hdim
    (fun i => centeredSegment (W i)) (markedTuple K U I) hcontain
  rw [← hWdet]
  refine (mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg n.factorial)).trans_eq ?_
  unfold allMarkedArray
  have hf : ((n - k).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n - k)
  field_simp

/-- A uniform bound on marked coefficients gives a uniform bound on all actual
`k`-minors once the repeated body contains a fixed inner ball. -/
theorem minorMaximum_bound {n k : ℕ} (hkn : k ≤ n)
    (K : Body n) (U : Fin n → Space n) {ρ B : ℝ}
    (hρ : 0 < ρ) (hB : 0 ≤ B)
    (hinner : closedBall 0 ρ ⊆ (K : Set (Space n)))
    (hcoeff : ∀ I : Deleted n k, allMarkedArray K U I ≤ B) :
    ProjectionVolumes.minorMaximum (columnsMatrix U) k ≤
      ((n - k).factorial : ℝ) * B / ρ ^ (n - k) := by
  by_cases hzero : ProjectionVolumes.minorMaximum (columnsMatrix U) k = 0
  · rw [hzero]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hB) (pow_nonneg hρ.le _)
  have hpos : 0 < ProjectionVolumes.minorMaximum (columnsMatrix U) k :=
    lt_of_le_of_ne (ProjectionVolumes.minorMaximum_nonneg _ _) (Ne.symm hzero)
  obtain ⟨I, J, hI, hJ, hmax⟩ :=
    ProjectionVolumes.exists_ordered_maximal_minor (columnsMatrix U) hpos
  have h := ordered_minor_bound hkn K U ⟨I, hI⟩ ⟨J, hJ⟩ hρ.le hinner
  rw [hmax] at h
  apply (le_div_iff₀ (pow_pos hρ _)).mpr
  rw [mul_comm]
  exact h.trans (mul_le_mul_of_nonneg_left (hcoeff ⟨I, hI⟩) (Nat.cast_nonneg _))

end RankThreeProjection

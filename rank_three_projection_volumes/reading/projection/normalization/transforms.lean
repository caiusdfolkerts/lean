module
public import Projection.Normalization.MatrixNormalization
public import Projection.Normalization.Compactness
public import Projection.SegmentDeterminant
public import TauCeti.Analysis.Convex.AffineNormalization

/-!
# Actual transformations of marked bodies

The first normalization is affine and places an arbitrary body with nonempty
interior between fixed concentric balls. The second is the maximal-minor row
normalization. Every transformation of the marks is accompanied by its exact
mixed-volume factor.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set Metric Module MeasureTheory
open scoped Pointwise BigOperators Matrix

namespace RankThreeProjection
open VolumePolynomials

/-- The continuous linear map represented by a real matrix in the coordinate
basis. -/
def matrixLinear {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Space n →L[ℝ] Space n :=
  (Matrix.toLin' M).toContinuousLinearMap

@[simp] theorem matrixLinear_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (x : Space n) : matrixLinear M x = M *ᵥ x := rfl

@[simp] theorem matrixLinear_det {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    LinearMap.det (matrixLinear M).toLinearMap = M.det := LinearMap.det_toLin' M

theorem allMarkedArray_smul_marks {n k : ℕ} (K : Body n) (U : Fin n → Space n)
    (g : ℝ) (hg : 0 ≤ g) (I : Deleted n k) :
    allMarkedArray K (fun i => g • U i) I = g ^ k * allMarkedArray K U I := by
  let c : Fin (n - k + k) → ℝ :=
    Fin.append (fun _ : Fin (n - k) => 1) (fun _ : Fin k => g)
  have hc : ∀ i, 0 ≤ c i := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [c, Fin.append_left] using (zero_le_one : (0 : ℝ) ≤ 1)
    · intro j
      simpa only [c, Fin.append_right] using hg
  have htuple : markedTuple K (fun i => g • U i) I =
      fun j => c j • markedTuple K U I j := by
    funext j
    refine Fin.addCases ?_ ?_ j
    · intro i
      simp only [markedTuple, c, Fin.append_left, one_smul]
    · intro i
      simp only [markedTuple, c, Fin.append_right, centeredSegment_smul]
  have hprod : (∏ j, c j) = g ^ k := by
    rw [Fin.prod_univ_add]
    simp only [c, Fin.append_left, Fin.append_right, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, one_pow, one_mul]
  unfold allMarkedArray
  rw [htuple, mixedVolume_independent_smul volume _ c hc, hprod]
  rw [mul_left_comm]

theorem allMarkedArray_smul_body {n k : ℕ} (K : Body n) (U : Fin n → Space n)
    (g : ℝ) (hg : 0 ≤ g) (I : Deleted n k) :
    allMarkedArray (g • K) U I = g ^ (n - k) * allMarkedArray K U I := by
  let c : Fin (n - k + k) → ℝ :=
    Fin.append (fun _ : Fin (n - k) => g) (fun _ : Fin k => 1)
  have hc : ∀ i, 0 ≤ c i := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [c, Fin.append_left] using hg
    · intro j
      simpa only [c, Fin.append_right] using (zero_le_one : (0 : ℝ) ≤ 1)
  have htuple : markedTuple (g • K) U I = fun j => c j • markedTuple K U I j := by
    funext j
    refine Fin.addCases ?_ ?_ j
    · intro i
      simp only [markedTuple, c, Fin.append_left]
    · intro i
      simp only [markedTuple, c, Fin.append_right, one_smul]
  have hprod : (∏ j, c j) = g ^ (n - k) := by
    rw [Fin.prod_univ_add]
    simp only [c, Fin.append_left, Fin.append_right, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, one_pow, mul_one]
  unfold allMarkedArray
  rw [htuple, mixedVolume_independent_smul volume _ c hc, hprod]
  rw [mul_left_comm]

theorem allMarkedArray_map {n k : ℕ} (K : Body n) (U : Fin n → Space n)
    (L : Space n →L[ℝ] Space n) (I : Deleted n k) :
    allMarkedArray (mapBody L K) (fun i => L (U i)) I =
      |LinearMap.det L.toLinearMap| * allMarkedArray K U I := by
  have htuple : markedTuple (mapBody L K) (fun i => L (U i)) I =
      fun j => mapBody L (markedTuple K U I j) := by
    funext j
    refine Fin.addCases ?_ ?_ j
    · intro i
      simp only [markedTuple, Fin.append_left]
    · intro i
      simp only [markedTuple, Fin.append_right, map_centeredSegment]
  unfold allMarkedArray
  rw [htuple, mixedVolume_map_linear volume L]
  rw [mul_left_comm]

theorem allMarkedArray_map_smul {n k : ℕ} (K : Body n) (U : Fin n → Space n)
    (L : Space n →L[ℝ] Space n) (g : ℝ) (hg : 0 ≤ g) (I : Deleted n k) :
    allMarkedArray (mapBody L K) (fun i => g • L (U i)) I =
      (g ^ k * |LinearMap.det L.toLinearMap|) * allMarkedArray K U I := by
  rw [allMarkedArray_smul_marks _ _ g hg, allMarkedArray_map, mul_assoc]

theorem allMarkedArray_translate_body {n k : ℕ} (K : Body n)
    (U : Fin n → Space n) (v : Space n) :
    allMarkedArray (k := k) (translateBody v K) U = allMarkedArray K U := by
  funext I
  let w : Fin (n - k + k) → Space n :=
    Fin.append (fun _ : Fin (n - k) => v) (fun _ : Fin k => 0)
  have htuple : markedTuple (translateBody v K) U I =
      fun j => translateBody (w j) (markedTuple K U I j) := by
    funext j
    refine Fin.addCases ?_ ?_ j
    · intro i
      simp only [markedTuple, w, Fin.append_left]
    · intro i
      simp only [markedTuple, w, Fin.append_right, translateBody_zero]
  unfold allMarkedArray
  rw [htuple, mixedVolume_translate]

/-- Entrywise bounded matrices have a uniform operator bound in the actual
coordinate sup norm. -/
theorem norm_matrixLinear_le {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : ∀ i j, |G i j| ≤ 1) (x : Space n) :
    ‖matrixLinear G x‖ ≤ (n : ℝ) * ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Nat.cast_nonneg n) (norm_nonneg x))).mpr
  intro i
  change ‖∑ j, G i j * x j‖ ≤ (n : ℝ) * ‖x‖
  calc
    ‖∑ j, G i j * x j‖ ≤ ∑ j, ‖G i j * x j‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖x j‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg (x j)) (hG i j)
    _ ≤ (n : ℝ) * ‖x‖ := by
      simpa only [Fintype.card_fin, nsmul_eq_mul] using Pi.sum_norm_apply_le_norm x

/-- Exact geometric use of the matrix normalizer. The hypothesis on the
`k`-minors is a concrete bound on determinants of the actual marked vectors.
-/
theorem normalize_marked_pair {n k : ℕ} (hk : 0 < k) {ρ D : ℝ}
    (K : Body n) (U : Fin n → Space n)
    (hinner : closedBall 0 ρ ⊆ (K : Set (Space n)))
    (houter : (K : Set (Space n)) ⊆ closedBall 0 1)
    (hminor : ProjectionVolumes.minorMaximum (columnsMatrix U) k ≤ D) :
    ∃ (L : Body n) (V : Fin n → Space n) (s : Finset (Fin n)),
      s.card < k ∧ coordinateDisk s ρ ⊆ (L : Set (Space n)) ∧
      (L : Set (Space n)) ⊆ closedBall 0 (n : ℝ) ∧ ‖V‖ ≤ max 1 D ∧
      allMarkedArray (k := k) L V = allMarkedArray K U := by
  obtain ⟨g, G, s, hg, _hdet, hs, hG, hGU, hscale, hfix⟩ :=
    ProjectionVolumes.exists_matrix_normalization hk (columnsMatrix U)
  let L := mapBody (matrixLinear G) K
  let V : Fin n → Space n := fun i => g • matrixLinear G (U i)
  refine ⟨L, V, s, hs, ?_, ?_, ?_, ?_⟩
  · intro x hx
    refine ⟨x, hinner (mem_closedBall_zero_iff.mpr hx.1), ?_⟩
    exact hfix x hx.2
  · rintro y ⟨x, hx, rfl⟩
    apply mem_closedBall_zero_iff.mpr
    have hnorm := mem_closedBall_zero_iff.mp (houter hx)
    exact (norm_matrixLinear_le G hG x).trans
      ((mul_le_mul_of_nonneg_left hnorm (Nat.cast_nonneg n)).trans_eq (mul_one _))
  · have hD : 0 ≤ max 1 D := zero_le_one.trans (le_max_left _ _)
    apply (pi_norm_le_iff_of_nonneg hD).mpr
    intro j
    apply (pi_norm_le_iff_of_nonneg hD).mpr
    intro i
    change |(g • (G * columnsMatrix U)) i j| ≤ max 1 D
    exact (hGU i j).trans (max_le_max le_rfl hminor)
  · funext I
    change allMarkedArray (mapBody (matrixLinear G) K)
      (fun i => g • matrixLinear G (U i)) I = _
    rw [allMarkedArray_map_smul K U (matrixLinear G) g (zero_le_one.trans hg),
      matrixLinear_det, hscale, one_mul]

/-- The affine image is represented using the existing literal linear image
and translation operations on convex bodies. -/
theorem affine_image_as_body {n : ℕ} (T : Space n ≃ᵃ[ℝ] Space n) (K : Body n) :
    T '' (K : Set (Space n)) =
      (translateBody (T 0) (mapBody T.linear.toContinuousLinearEquiv.toContinuousLinearMap K) :
        Set (Space n)) := by
  ext y
  simp only [coe_translateBody, coe_mapBody, Set.mem_vadd_set]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨T.linear x, ⟨x, hx, rfl⟩, ?_⟩
    simpa only [vadd_eq_add, add_zero, add_comm] using (T.map_vadd 0 x).symm
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨x, hx, ?_⟩
    change T x = T 0 + T.linear x
    simpa only [vadd_eq_add, add_zero, add_comm] using T.map_vadd 0 x

/-- Uniform affine normalization with marked coefficients preserved exactly.
The inner radius depends only on the ambient coordinate space. -/
theorem exists_affine_normalized_marked_pairs (n : ℕ) :
    ∃ ρ > 0, ∀ (k : ℕ), 0 < k → ∀ (K : Body n) (U : Fin n → Space n),
      (interior (K : Set (Space n))).Nonempty →
      ∃ (L : Body n) (V : Fin n → Space n),
        closedBall 0 ρ ⊆ (L : Set (Space n)) ∧
        (L : Set (Space n)) ⊆ closedBall 0 1 ∧
        allMarkedArray (k := k) L V = allMarkedArray K U := by
  obtain ⟨r, hr, hnormal⟩ :=
    TauCeti.exists_affineEquiv_ball_subset_image_subset_ball (Space n)
  refine ⟨r / 2, half_pos hr, ?_⟩
  intro k hk K U hKint
  obtain ⟨T, hinner, houter⟩ := hnormal (K : Set (Space n)) K.convex K.isBounded hKint
  let A := T.linear.toContinuousLinearEquiv.toContinuousLinearMap
  let d : ℝ := |LinearMap.det A.toLinearMap|
  have hd : 0 < d := abs_pos.mpr T.linear.isUnit_det'.ne_zero
  let a : ℝ := d ^ ((k : ℝ)⁻¹)
  have ha : 0 < a := Real.rpow_pos_of_pos hd _
  have hscale : (a⁻¹) ^ k * d = 1 := by
    rw [inv_pow, Real.rpow_inv_natCast_pow hd.le hk.ne', inv_mul_cancel₀ hd.ne']
  let L := translateBody (T 0) (mapBody A K)
  let V : Fin n → Space n := fun i => a⁻¹ • A (U i)
  have heq : T '' (K : Set (Space n)) = (L : Set (Space n)) := affine_image_as_body T K
  refine ⟨L, V, ?_, ?_, ?_⟩
  · rw [← heq]
    exact (closedBall_subset_ball (half_lt_self hr)).trans hinner
  · rw [← heq]
    exact houter.trans ball_subset_closedBall
  · rw [allMarkedArray_translate_body]
    funext I
    rw [allMarkedArray_map_smul K U A a⁻¹ (inv_nonneg.mpr ha.le), hscale, one_mul]

end RankThreeProjection

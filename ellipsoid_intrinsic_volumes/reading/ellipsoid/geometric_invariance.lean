module

public import Ellipsoid.JacobianSphereCoefficient
public import Mathlib.MeasureTheory.Group.Measure

@[expose] public section

noncomputable section

open MeasureTheory Set Polynomial
open scoped BigOperators Pointwise

namespace EllipsoidVerification

@[simp] theorem unitBallVolume_zero : unitBallVolume 0 = 1 := by
  simp [unitBallVolume, volume_euclideanSpace_eq_dirac]

theorem unitBallVolume_eq (n : ℕ) :
    unitBallVolume n = (Real.sqrt Real.pi) ^ n / Real.Gamma ((n : ℝ) / 2 + 1) := by
  cases n with
  | zero => simp
  | succ n =>
    rw [unitBallVolume, EuclideanSpace.volume_closedBall (Fin (n + 1))]
    simp only [ENNReal.ofReal_one, one_pow, one_mul, Fintype.card_fin]
    exact ENNReal.toReal_ofReal (by positivity)

theorem unitBallVolume_pos (n : ℕ) : 0 < unitBallVolume n := by
  rw [unitBallVolume_eq]
  positivity

theorem parallelBody_rigidImage {n : ℕ} (c : Space n) (U : Space n ≃ₗᵢ[ℝ] Space n)
    (K : Set (Space n)) (r : ℝ) :
    parallelBody ((fun x => c + U x) '' K) r =
      (fun x => c + U x) '' parallelBody K r := by
  ext z
  constructor
  · rintro ⟨v, ⟨x, hx, rfl⟩, w, hw, heq⟩
    refine ⟨x + U.symm w, ⟨x, hx, U.symm w, ?_, rfl⟩, ?_⟩
    · simpa only [Metric.mem_closedBall, dist_zero_right, U.symm.norm_map] using hw
    · simpa only [map_add, U.apply_symm_apply, add_assoc] using heq
  · rintro ⟨v, ⟨x, hx, w, hw, rfl⟩, rfl⟩
    refine ⟨c + U x, ⟨x, hx, rfl⟩, U w, ?_, ?_⟩
    · simpa only [Metric.mem_closedBall, dist_zero_right, U.norm_map] using hw
    · simp only [map_add, add_assoc]

theorem volume_rigidImage {n : ℕ} (c : Space n) (U : Space n ≃ₗᵢ[ℝ] Space n)
    {K : Set (Space n)} (hK : IsCompact K) :
    volume ((fun x => c + U x) '' K) = volume K := by
  have hMP : MeasurePreserving (fun x : Space n => c + U x) :=
    (measurePreserving_add_left volume c).comp U.measurePreserving
  have hinj : Function.Injective (fun x : Space n => c + U x) :=
    fun x y hxy => U.injective (add_left_cancel hxy)
  have hcont : Continuous (fun x : Space n => c + U x) :=
    continuous_const.add U.continuous
  have h := hMP.measure_preimage (s := (fun x : Space n => c + U x) '' K)
    (hK.image hcont).measurableSet.nullMeasurableSet
  simpa only [Set.preimage_image_eq _ hinj] using h.symm

theorem parallelVolume_rigidImage {n : ℕ} (c : Space n) (U : Space n ≃ₗᵢ[ℝ] Space n)
    {K : Set (Space n)} (hK : IsCompact K) (r : ℝ) :
    parallelVolume ((fun x => c + U x) '' K) r = parallelVolume K r := by
  change (volume (parallelBody ((fun x => c + U x) '' K) r)).toReal =
    (volume (parallelBody K r)).toReal
  rw [parallelBody_rigidImage]
  have hcompact : IsCompact (parallelBody K r) := by
    change IsCompact (K + Metric.closedBall 0 r)
    exact hK.add (isCompact_closedBall 0 r)
  exact congrArg ENNReal.toReal (volume_rigidImage c U hcompact)

theorem FullEllipsoid.body_eq_rigidImage {n : ℕ} (E : FullEllipsoid n) :
    E.body = (fun x => E.center + E.frame x) '' axisBody E.semiaxis := by
  simp [FullEllipsoid.body, axisBody, Set.image_image]

theorem isCompact_axisBody {n : ℕ} (a : Fin n → ℝ) : IsCompact (axisBody a) :=
  (isCompact_closedBall (0 : Space n) 1).image (continuous_axisMap a)

theorem FullEllipsoid.steinerInterpolant_eq_axes {n : ℕ} (E : FullEllipsoid n) :
    steinerInterpolant E.body = steinerInterpolant (axisBody E.semiaxis) := by
  apply Lagrange.interpolate_eq_of_values_eq_on
  intro i hi
  rw [E.body_eq_rigidImage,
    parallelVolume_rigidImage E.center E.frame (isCompact_axisBody E.semiaxis)]

theorem FullEllipsoid.volume_eq_axes {n : ℕ} (E : FullEllipsoid n) (k : ℕ) :
    E.volume k = intrinsicVolume (axisBody E.semiaxis) k := by
  simp only [FullEllipsoid.volume, intrinsicVolume, E.steinerInterpolant_eq_axes]

theorem FullEllipsoid.hasSteinerFormula {n : ℕ} (hn : 0 < n) (E : FullEllipsoid n) :
    HasSteinerFormula E.body := by
  intro r hr
  rw [E.body_eq_rigidImage,
    parallelVolume_rigidImage E.center E.frame (isCompact_axisBody E.semiaxis)]
  rw [← E.body_eq_rigidImage, E.steinerInterpolant_eq_axes]
  exact axisBody_hasSteinerFormula hn E.semiaxis_pos r hr

theorem intrinsicVolume_top_of_hasSteinerFormula {n : ℕ} {K : Set (Space n)}
    (hK : HasSteinerFormula K) : intrinsicVolume K n = (volume K).toReal := by
  rw [intrinsicVolume, if_pos le_rfl, Nat.sub_self, unitBallVolume_zero, div_one,
    Polynomial.coeff_zero_eq_eval_zero, ← hK 0 le_rfl]
  simp [parallelVolume, parallelBody]

theorem axisLinear_det {n : ℕ} (a : Fin n → ℝ) : LinearMap.det (axisLinear a) = ∏ i, a i := by
  have hM : axisLinear a = (Matrix.diagonal a).toEuclideanLin := by
    ext x i
    simp [axisLinear, axisMap, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
      Matrix.mulVec_diagonal]
  rw [hM]
  change (Matrix.toLpLin 2 2 (Matrix.diagonal a)).det = ∏ i, a i
  rw [LinearMap.det_toLpLin, Matrix.det_diagonal]

theorem volume_axisBody {n : ℕ} {a : Fin n → ℝ} (ha : ∀ i, 0 < a i) :
    (volume (axisBody a)).toReal = unitBallVolume n * ∏ i, a i := by
  have h := MeasureTheory.Measure.addHaar_image_linearMap (volume : Measure (Space n))
    (axisLinear a) (Metric.closedBall 0 1)
  change volume (axisBody a) = _ at h
  rw [h, axisLinear_det, abs_of_pos (Finset.prod_pos fun i _ => ha i), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Finset.prod_nonneg fun i _ => (ha i).le)]
  exact mul_comm _ _

theorem FullEllipsoid.volume_top {n : ℕ} (hn : 0 < n) (E : FullEllipsoid n) :
    E.volume n = unitBallVolume n * ∏ i, E.semiaxis i := by
  rw [E.volume_eq_axes, intrinsicVolume_top_of_hasSteinerFormula
    (axisBody_hasSteinerFormula hn E.semiaxis_pos), volume_axisBody E.semiaxis_pos]

end EllipsoidVerification

module

public import VolumePolynomials.GeometricCornerFamily
public import VolumePolynomials.FiniteCornerMeasures
public import VolumePolynomials.CompactKernelMass

@[expose] public section
set_option autoImplicit false

/-! # The actual measures of the geometrically separated finite caps -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal MeasureTheory

namespace VolumePolynomials.HalfZonotope

open PlanarExtrusion

theorem rawGeometricGenerators_product (n : ℕ) :
    ∀ v ∈ rawGeometricGenerators n,
      4 * (v.1 * (-v.2)) = (4 : ℝ) ^ n := by
  first
  | induction n with
    | zero => simp [rawGeometricGenerators]
    | succ n ih =>
        intro v hv
        simp only [rawGeometricGenerators, List.mem_cons, List.mem_map] at hv
        rcases hv with rfl | ⟨w, hw, rfl⟩
        · simp [pow_succ, mul_comm]
        · have h := ih w hw
          simp only [stretchHorizontal_apply, pow_succ]
          nlinarith

def geometricWeight (n : ℕ) : ℝ :=
  geometricNormalizer n * Real.sqrt ((4 : ℝ) ^ n) / 2

theorem geometricWeight_nonneg {n : ℕ} (hn : 0 < n) :
    0 ≤ geometricWeight n := by
  first
  | exact div_nonneg (mul_nonneg (geometricNormalizer_pos hn).le (Real.sqrt_nonneg _))
      (by norm_num)

theorem geometricWeight_sq (n : ℕ) :
    geometricWeight n ^ 2 = geometricNormalizer n ^ 2 * (4 : ℝ) ^ n / 4 := by
  first
  | simp only [geometricWeight, div_pow, mul_pow,
      Real.sq_sqrt (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) n)]
    norm_num

theorem edgeWeight_geometric {n : ℕ} (hn : 0 < n)
    {v : Plane} (hv : v ∈ geometricGenerators n) :
    (edgeWeight v : ℝ) = geometricWeight n := by
  first
  | obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    have hs := rawGeometricGenerators_signed n w hw
    have hp := rawGeometricGenerators_product n w hw
    have hprod : 0 ≤ (geometricNormalizer n • w).1 *
        (-(geometricNormalizer n • w).2) := by
      first
      | simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        exact mul_nonneg (mul_nonneg (geometricNormalizer_pos hn).le hs.1)
          (neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos
            (geometricNormalizer_pos hn).le hs.2))
    have hsq : (edgeWeight (geometricNormalizer n • w) : ℝ) ^ 2 =
        geometricWeight n ^ 2 := by
      first
      | change (Real.sqrt ((geometricNormalizer n • w).1 *
          (-(geometricNormalizer n • w).2))) ^ 2 = _
        rw [Real.sq_sqrt hprod, geometricWeight_sq]
        simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        nlinarith [congrArg (geometricNormalizer n ^ 2 * ·) hp]
    exact (sq_eq_sq₀ (edgeWeight _).coe_nonneg (geometricWeight_nonneg hn)).mp hsq

@[simp] theorem edgeMeasure_real_univ (v : Plane) :
    (edgeMeasure v).real univ = (edgeWeight v : ℝ) := by
  first
  | simp [edgeMeasure]

theorem cornerMeasure_real_univ (vs : List Plane) :
    (cornerMeasure vs).real univ = (vs.map (fun v => (edgeWeight v : ℝ))).sum := by
  first
  | induction vs with
    | nil => simp [cornerMeasure]
    | cons v vs ih => simp [cornerMeasure, measureReal_add_apply, ih, add_comm]

theorem geometric_cornerMeasure_mass {n : ℕ} (hn : 0 < n) :
    (cornerMeasure (geometricGenerators n)).real univ = (n : ℝ) * geometricWeight n := by
  first
  | rw [cornerMeasure_real_univ]
    have he : (geometricGenerators n).map (fun v => (edgeWeight v : ℝ)) =
        (geometricGenerators n).map (fun _ => geometricWeight n) := by
      first
      | apply List.map_congr_left
        intro v hv
        exact edgeWeight_geometric hn hv
    rw [he, List.map_const', List.sum_replicate]
    simp [geometricGenerators, nsmul_eq_mul]

theorem edgeSlope_pos_smul {t : ℝ} (ht : 0 < t) (v : Plane) :
    edgeSlope (t • v) = edgeSlope v := by
  first
  | unfold edgeSlope
    congr 1
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    rw [neg_mul_eq_mul_neg, mul_div_mul_left _ _ ht.ne']

theorem rawGeometricGenerators_slope_bounds {n : ℕ}
    {v : Plane} (hv : v ∈ rawGeometricGenerators n) :
    edgeSlope v ∈ Icc (-(n : ℝ) * Real.log 4) ((n : ℝ) * Real.log 4) := by
  first
  | obtain ⟨ha, hb, hA, hB⟩ := rawGeometricGenerators_bounds n v hv
    have hpow : (0 : ℝ) < 4 ^ n := pow_pos (by norm_num) n
    have hapos : 0 < v.1 := by linarith
    have hbpos : 0 < -v.2 := by linarith
    have hpowone : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
    have hrlo : 1 / (4 : ℝ) ^ n ≤ (-v.2) / v.1 := by
      first
      | apply (div_le_div_iff₀ hpow hapos).mpr
        nlinarith
    have hrhi : (-v.2) / v.1 ≤ (4 : ℝ) ^ n := by
      first
      | apply (div_le_iff₀ hapos).mpr
        nlinarith
    have hlo := Real.log_le_log (div_pos (by norm_num) hpow) hrlo
    have hhi := Real.log_le_log (div_pos hbpos hapos) hrhi
    rw [Real.log_div one_ne_zero hpow.ne', Real.log_one, Real.log_pow] at hlo
    rw [Real.log_pow] at hhi
    exact ⟨by simpa [edgeSlope] using hlo, by simpa [edgeSlope] using hhi⟩

theorem geometricGenerators_slope_bounds {n : ℕ} (hn : 0 < n)
    {v : Plane} (hv : v ∈ geometricGenerators n) :
    edgeSlope v ∈ Icc (-(n : ℝ) * Real.log 4) ((n : ℝ) * Real.log 4) := by
  first
  | obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    rw [edgeSlope_pos_smul (geometricNormalizer_pos hn)]
    exact rawGeometricGenerators_slope_bounds hw

theorem cornerMeasure_support {vs : List Plane} {s : Set ℝ}
    (hs : MeasurableSet s) (hvs : ∀ v ∈ vs, edgeSlope v ∈ s) :
    ∀ᵐ x ∂cornerMeasure vs, x ∈ s := by
  first
  | induction vs with
    | nil => simp [cornerMeasure]
    | cons v vs ih =>
        rw [cornerMeasure, ae_add_measure_iff]
        refine ⟨ih (fun w hw => hvs w (List.mem_cons_of_mem v hw)), ?_⟩
        apply Measure.ae_smul_measure _ (edgeWeight v)
        exact (ae_dirac_iff hs).mpr (hvs v List.mem_cons_self)

theorem geometric_cornerMeasure_support {n : ℕ} (hn : 0 < n) :
    ∀ᵐ x ∂cornerMeasure (geometricGenerators n),
      x ∈ Icc (-((n : ℝ) * Real.log 4)) ((n : ℝ) * Real.log 4) := by
  first
  | apply cornerMeasure_support measurableSet_Icc
    intro v hv
    simpa only [neg_mul] using geometricGenerators_slope_bounds hn hv

def geometricConvolutionDeficit (n : ℕ) : ℝ :=
  ‖cornerMean (cornerMeasure (geometricGenerators n) ∗
    cornerMeasure (geometricGenerators n))‖ ^ 2 / 2

theorem geometricConvolutionDeficit_nonneg (n : ℕ) :
    0 ≤ geometricConvolutionDeficit n := div_nonneg (sq_nonneg _) (by norm_num)

theorem geometricConvolution_mass_bound {n : ℕ} (hn : 0 < n) :
    ((n : ℝ) * geometricWeight n) ^ 4 ≤
      2 * (1 + (n : ℝ) * Real.log 4) * geometricConvolutionDeficit n := by
  first
  | have hR : 0 ≤ (n : ℝ) * Real.log 4 :=
      mul_nonneg (Nat.cast_nonneg n) (Real.log_nonneg (by norm_num))
    have h := compact_convolution_mass_fourth_le_energy hR
      (cornerMeasure (geometricGenerators n)) (geometric_cornerMeasure_support hn)
    rw [geometric_cornerMeasure_mass hn] at h
    dsimp only [geometricConvolutionDeficit]
    nlinarith

theorem log_four_le_two : Real.log (4 : ℝ) ≤ 2 := by
  first
  | have h : Real.log (2 : ℝ) ≤ 1 := by
      first
      | have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        linarith
    have he : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      first
      | convert Real.log_pow (2 : ℝ) 2 using 1 <;> norm_num
    rw [he]
    linarith

theorem geometricDeficit_weight_bounds (n : ℕ) :
    (n : ℝ) * geometricWeight n ^ 2 / 2 ≤ geometricDeficit n ∧
      geometricDeficit n ≤ (5 / 6) * (n : ℝ) * geometricWeight n ^ 2 := by
  first
  | have h := geometricDeficit_weighted_bounds n
    rw [geometricWeight_sq]
    constructor <;> nlinarith

/-- A bound of logarithmic size on the full unbounded finite family. The
quantity on the left is the genuine exponential-kernel convolution energy. -/
theorem geometricConvolutionDeficit_lower {n : ℕ} (hn : 0 < n) :
    (6 / 25) * (n : ℝ) * geometricDeficit n ^ 2 ≤ geometricConvolutionDeficit n := by
  first
  | have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hδ := geometricDeficit_nonneg hn
    have hη := geometricConvolutionDeficit_nonneg n
    have hw := geometricWeight_nonneg hn
    have hupper := (geometricDeficit_weight_bounds n).2
    have hsq : geometricDeficit n ^ 2 ≤
        ((5 / 6) * (n : ℝ) * geometricWeight n ^ 2) ^ 2 := by
      first
      | exact (sq_le_sq₀ hδ (by positivity)).mpr hupper
    have hmass := geometricConvolution_mass_bound hn
    have hlog : 1 + (n : ℝ) * Real.log 4 ≤ 3 * n := by
      first
      | nlinarith [mul_le_mul_of_nonneg_left log_four_le_two hn0.le]
    have hηbound : ((n : ℝ) * geometricWeight n) ^ 4 ≤
        6 * n * geometricConvolutionDeficit n := by
      first
      | nlinarith [mul_le_mul_of_nonneg_right hlog hη]
    have hsquared := mul_le_mul_of_nonneg_left hsq (sq_nonneg (n : ℝ))
    have hfinal : (n : ℝ) * ((6 / 25) * n * geometricDeficit n ^ 2) ≤
        (n : ℝ) * geometricConvolutionDeficit n := by
      first
      | nlinarith
    exact Iff.mp (mul_le_mul_iff_right₀ hn0) hfinal

end VolumePolynomials.HalfZonotope

module

public import VolumePolynomials.FiniteCornerCaps
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section
set_option autoImplicit false

/-! # An unbounded finite family with geometrically separated corner slopes -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace VolumePolynomials.HalfZonotope

open PlanarExtrusion

def stretchHorizontal (t : ℝ) : Plane →ₗ[ℝ] Plane where
  toFun v := (t * v.1, v.2)
  map_add' := by intro x y; ext <;> simp <;> ring
  map_smul' := by intro a x; ext <;> simp <;> ring

@[simp] theorem stretchHorizontal_apply (t : ℝ) (v : Plane) :
    stretchHorizontal t v = (t * v.1, v.2) := rfl

theorem cornerInteraction_stretch {t : ℝ} (ht : 0 ≤ t) (v w : Plane) :
    cornerInteraction (stretchHorizontal t v) (stretchHorizontal t w) =
      t * cornerInteraction v w := by
  first
  | simp only [cornerInteraction, stretchHorizontal_apply, mul_assoc]
    exact (mul_min_of_nonneg _ _ ht).symm

theorem cornerEnergy_stretch {t : ℝ} (ht : 0 ≤ t) (vs : List Plane) :
    cornerEnergy (vs.map (stretchHorizontal t)) = t * cornerEnergy vs := by
  first
  | induction vs with
    | nil => simp [cornerEnergy]
    | cons v vs ih =>
        simp only [List.map_cons, cornerEnergy, ih, List.map_map, Function.comp_def]
        simp only [cornerInteraction_stretch ht]
        rw [List.sum_map_mul_left]
        simp only [stretchHorizontal_apply]
        ring

/-- The list consists of `(4^i,-4^(n-1-i))` for `0≤i<n`; the recursive
definition avoids truncated natural subtraction in subsequent proofs. -/
def rawGeometricGenerators : ℕ → List Plane
  | 0 => []
  | n + 1 => (1, -(4 : ℝ) ^ n) ::
      (rawGeometricGenerators n).map (stretchHorizontal 4)

@[simp] theorem rawGeometricGenerators_length (n : ℕ) :
    (rawGeometricGenerators n).length = n := by
  first
  | induction n with
    | zero => rfl
    | succ n ih => simp [rawGeometricGenerators, ih]

theorem rawGeometricGenerators_sum (n : ℕ) :
    (rawGeometricGenerators n).sum =
      (((4 : ℝ) ^ n - 1) / 3, -((4 : ℝ) ^ n - 1) / 3) := by
  first
  | induction n with
    | zero => ext <;> norm_num [rawGeometricGenerators]
    | succ n ih =>
        rw [rawGeometricGenerators, List.sum_cons, ← map_list_sum, ih]
        ext <;> simp only [Prod.fst_add, Prod.snd_add, stretchHorizontal_apply, pow_succ] <;>
          ring

theorem rawGeometricGenerators_bounds (n : ℕ) :
    ∀ v ∈ rawGeometricGenerators n,
      1 ≤ v.1 ∧ 1 ≤ -v.2 ∧ v.1 ≤ (4 : ℝ) ^ n ∧ -v.2 ≤ (4 : ℝ) ^ n := by
  first
  | induction n with
    | zero => simp [rawGeometricGenerators]
    | succ n ih =>
        intro v hv
        have hp : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
        simp only [rawGeometricGenerators, List.mem_cons, List.mem_map] at hv
        rcases hv with rfl | ⟨w, hw, rfl⟩
        · simp only [neg_neg, pow_succ]
          exact ⟨le_rfl, hp, by nlinarith, by nlinarith⟩
        · obtain ⟨h1, h2, h3, h4⟩ := ih w hw
          simp only [stretchHorizontal_apply, pow_succ]
          exact ⟨by linarith, h2, by linarith, by nlinarith⟩

theorem rawGeometricGenerators_signed (n : ℕ) :
    ∀ v ∈ rawGeometricGenerators n, 0 ≤ v.1 ∧ v.2 ≤ 0 := by
  first
  | intro v hv
    have h := rawGeometricGenerators_bounds n v hv
    exact ⟨by linarith [h.1], by linarith [h.2.1]⟩

theorem sum_neg_snd (vs : List Plane) :
    (vs.map (fun v => -v.2)).sum = -vs.sum.2 := by
  first
  | induction vs with
    | nil => simp
    | cons v vs ih => simp [ih, add_comm]

theorem raw_corner_cross_sum (n : ℕ) :
    (((rawGeometricGenerators n).map (stretchHorizontal 4)).map
      (cornerInteraction (1, -(4 : ℝ) ^ n))).sum = ((4 : ℝ) ^ n - 1) / 3 := by
  first
  | have heq : ((rawGeometricGenerators n).map (stretchHorizontal 4)).map
        (cornerInteraction (1, -(4 : ℝ) ^ n)) =
          (rawGeometricGenerators n).map (fun v => -v.2) := by
      first
      | rw [List.map_map]
        apply List.map_congr_left
        intro v hv
        obtain ⟨h1, h2, h3, h4⟩ := rawGeometricGenerators_bounds n v hv
        have hp : (0 : ℝ) ≤ 4 ^ n := pow_nonneg (by norm_num) n
        have hprod := mul_nonneg (by linarith : 0 ≤ 4 * v.1 - 1) hp
        simp only [Function.comp_apply, cornerInteraction, stretchHorizontal_apply,
          one_mul, neg_neg]
        exact min_eq_left (by nlinarith)
    rw [heq, sum_neg_snd, rawGeometricGenerators_sum]
    ring

theorem raw_cornerEnergy_succ (n : ℕ) :
    cornerEnergy (rawGeometricGenerators (n + 1)) =
      4 * cornerEnergy (rawGeometricGenerators n) + (4 : ℝ) ^ n +
        2 * (((4 : ℝ) ^ n - 1) / 3) := by
  first
  | rw [rawGeometricGenerators, cornerEnergy, cornerEnergy_stretch (by norm_num),
      raw_corner_cross_sum]
    simp

/-- Bounds valid for every index, including zero. -/
theorem raw_cornerEnergy_bounds (n : ℕ) :
    (n : ℝ) * (4 : ℝ) ^ n ≤ 4 * cornerEnergy (rawGeometricGenerators n) ∧
      4 * cornerEnergy (rawGeometricGenerators n) ≤
        (5 / 3) * (n : ℝ) * (4 : ℝ) ^ n := by
  first
  | induction n with
    | zero => norm_num [rawGeometricGenerators, cornerEnergy]
    | succ n ih =>
        have hp : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
        rw [raw_cornerEnergy_succ]
        simp only [Nat.cast_add, Nat.cast_one, pow_succ]
        constructor <;> nlinarith [ih.1, ih.2]

def geometricNormalizer (n : ℕ) : ℝ := 3 / ((4 : ℝ) ^ n - 1)

def geometricGenerators (n : ℕ) : List Plane :=
  (rawGeometricGenerators n).map (fun v => geometricNormalizer n • v)

theorem geometricNormalizer_pos {n : ℕ} (hn : 0 < n) : 0 < geometricNormalizer n := by
  first
  | apply div_pos (by norm_num)
    exact sub_pos.mpr (one_lt_pow₀ (by norm_num : (1 : ℝ) < 4) hn.ne')

theorem geometricNormalizer_identity {n : ℕ} (hn : 0 < n) :
    geometricNormalizer n * ((4 : ℝ) ^ n - 1) = 3 := by
  first
  | unfold geometricNormalizer
    exact div_mul_cancel₀ _ (sub_ne_zero.mpr
      (ne_of_gt (one_lt_pow₀ (by norm_num : (1 : ℝ) < 4) hn.ne')))

theorem geometricGenerators_sum {n : ℕ} (hn : 0 < n) :
    (geometricGenerators n).sum = (1, -1) := by
  first
  | rw [geometricGenerators, ← List.smul_sum, rawGeometricGenerators_sum]
    have h := geometricNormalizer_identity hn
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> nlinarith

theorem geometricGenerators_signed {n : ℕ} (hn : 0 < n) :
    ∀ v ∈ geometricGenerators n, 0 ≤ v.1 ∧ v.2 ≤ 0 := by
  first
  | intro v hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    have h := rawGeometricGenerators_signed n w hw
    exact ⟨mul_nonneg (geometricNormalizer_pos hn).le h.1,
      mul_nonpos_of_nonneg_of_nonpos (geometricNormalizer_pos hn).le h.2⟩

def geometricDeficit (n : ℕ) : ℝ := cornerEnergy (geometricGenerators n) / 2

theorem geometricDeficit_formula (n : ℕ) :
    geometricDeficit n = geometricNormalizer n ^ 2 *
      cornerEnergy (rawGeometricGenerators n) / 2 := by
  first
  | rw [geometricDeficit, geometricGenerators, cornerEnergy_smul]

theorem geometricDeficit_nonneg {n : ℕ} (hn : 0 < n) : 0 ≤ geometricDeficit n :=
  div_nonneg (cornerEnergy_nonneg (geometricGenerators_signed hn)) (by norm_num)

/-- The deficit is that of the actual unit-width compact convex cap. -/
theorem area_geometricCap {n : ℕ} (hn : 0 < n) :
    volume.real (cap (geometricGenerators n)) = 1 / 2 - geometricDeficit n := by
  first
  | exact area_unit_cap (geometricGenerators_sum hn)

theorem geometricDeficit_weighted_bounds (n : ℕ) :
    geometricNormalizer n ^ 2 * (n : ℝ) * (4 : ℝ) ^ n / 8 ≤ geometricDeficit n ∧
      geometricDeficit n ≤ 5 * geometricNormalizer n ^ 2 * (n : ℝ) * (4 : ℝ) ^ n / 24 := by
  first
  | have h := raw_cornerEnergy_bounds n
    have hlow := mul_le_mul_of_nonneg_left h.1 (sq_nonneg (geometricNormalizer n))
    have hupp := mul_le_mul_of_nonneg_left h.2 (sq_nonneg (geometricNormalizer n))
    rw [geometricDeficit_formula]
    constructor <;> nlinarith

theorem geometricNormalizer_scaled_bounds {n : ℕ} (hn : 0 < n) :
    3 ≤ geometricNormalizer n * (4 : ℝ) ^ n ∧
      geometricNormalizer n * (4 : ℝ) ^ n ≤ 4 := by
  first
  | have hk := geometricNormalizer_pos hn
    have hidentity := geometricNormalizer_identity hn
    have hpow : (4 : ℝ) ≤ 4 ^ n := by
      first
      | simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hn
    have hk1 : geometricNormalizer n ≤ 1 := by
      first
      | unfold geometricNormalizer
        apply (div_le_one (by linarith : 0 < (4 : ℝ) ^ n - 1)).mpr
        linarith
    constructor <;> nlinarith

/-- Exponential lower control needed to turn the first crossing into a
logarithmic bound; no monotonicity of the deficit sequence is assumed. -/
theorem geometricDeficit_bounds {n : ℕ} (hn : 0 < n) :
    ((4 : ℝ) ^ n)⁻¹ ≤ geometricDeficit n ∧
      geometricDeficit n ≤ (10 / 3) * (n : ℝ) / (4 : ℝ) ^ n := by
  first
  | have hp : (0 : ℝ) < 4 ^ n := pow_pos (by norm_num) n
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hk := geometricNormalizer_scaled_bounds hn
    have hweight := geometricDeficit_weighted_bounds n
    have hsqlo : 9 ≤ (geometricNormalizer n * (4 : ℝ) ^ n) ^ 2 := by nlinarith
    have hsqup : (geometricNormalizer n * (4 : ℝ) ^ n) ^ 2 ≤ 16 := by nlinarith
    have hlo := mul_le_mul_of_nonneg_right hweight.1 hp.le
    have hup := mul_le_mul_of_nonneg_right hweight.2 hp.le
    have hnl := mul_le_mul_of_nonneg_left hsqlo hn0
    have hnu := mul_le_mul_of_nonneg_left hsqup hn0
    constructor
    · apply (inv_le_iff_one_le_mul₀ hp).mpr
      nlinarith
    · apply (le_div_iff₀ hp).mpr
      nlinarith

theorem geometricDeficit_tendsto_zero : Tendsto geometricDeficit atTop (𝓝 0) := by
  first
  | have hupper : Tendsto (fun n : ℕ => (10 / 3 : ℝ) * (n : ℝ) / (4 : ℝ) ^ n)
        atTop (𝓝 0) := by
      first
      | simpa [pow_one, mul_div_assoc] using
          (tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 4)).const_mul
            (10 / 3 : ℝ)
    apply squeeze_zero' _ _ hupper
    · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      exact geometricDeficit_nonneg hn
    · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      exact (geometricDeficit_bounds hn).2

end VolumePolynomials.HalfZonotope

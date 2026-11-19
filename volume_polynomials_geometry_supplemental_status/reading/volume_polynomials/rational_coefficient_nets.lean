module

public import VolumePolynomials.RationalGridBodies
public import VolumePolynomials.CoefficientModulus
public import VolumePolynomials.VolumePolynomialExistence
public import VolumePolynomials.RealizationContinuity
public import VolumePolynomials.QuadraticSeparation
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

@[expose] public section
set_option autoImplicit false

/-!
# Certified computable finite nets of actual volume-polynomial coefficients

The finite list of rational hull tuples is evaluated by the terminating
rational box-volume algorithm. Exact interpolation gives rational coefficient
centers. The explicit Hausdorff coefficient modulus supplies the uniform
covering bound, while every center is close to an actual bounded realization.
This constructs the geometric/computational Model required by Section 8.
-/

open Set Filter Metric
open scoped BigOperators Topology

namespace VolumePolynomials.RationalCoefficientNets

open RationalHulls

def samplingTolerance (k : ℕ) : ℚ := 1 / ((k : ℚ) + 1)

theorem samplingTolerance_pos (k : ℕ) : 0 < samplingTolerance k := by
  first
  | unfold samplingTolerance
    positivity

def gridMultiplier (n d : ℕ) : ℕ := ⌈interpolationWeightBound n d⌉₊ + 1

def resolution (n d k : ℕ) : ℕ := gridMultiplier n d * (k + 1)

theorem gridMultiplier_pos (n d : ℕ) : 0 < gridMultiplier n d := by
  first
  | unfold gridMultiplier
    omega

theorem weightBound_le_gridMultiplier (n d : ℕ) :
    interpolationWeightBound n d ≤ (gridMultiplier n d : ℚ) := by
  first
  | exact (Nat.le_ceil _).trans (by simp [gridMultiplier])

theorem resolution_bounds (n d k : ℕ) :
    1 / ((resolution n d k : ℝ) + 1) ≤ (samplingTolerance k : ℝ) ∧
      (1 / ((resolution n d k : ℝ) + 1)) * (interpolationWeightBound n d : ℝ) ≤ 1 := by
  first
  | have hA : (1 : ℝ) ≤ gridMultiplier n d := by exact_mod_cast gridMultiplier_pos n d
    have hT : (interpolationWeightBound n d : ℝ) ≤ gridMultiplier n d := by
      exact_mod_cast weightBound_le_gridMultiplier n d
    have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg k)
    have hres : (resolution n d k : ℝ) + 1 =
        (gridMultiplier n d : ℝ) * ((k : ℝ) + 1) + 1 := by simp [resolution]
    have hd : 0 < (resolution n d k : ℝ) + 1 := by positivity
    constructor
    · simp only [samplingTolerance, Rat.cast_div, Rat.cast_one, Rat.cast_add, Rat.cast_natCast]
      apply one_div_le_one_div_of_le (by positivity)
      rw [hres]
      nlinarith
    · rw [one_div, inv_mul_eq_div, div_le_one hd]
      rw [hres]
      nlinarith

def coordinateBudget (n d R : ℕ) : ℚ :=
  coefficientExtractionBound n d + coefficientModulus n d (R : ℚ) + 1

theorem coefficientModulus_nonneg (n d R : ℕ) : 0 ≤ coefficientModulus n d (R : ℚ) := by
  first
  | have hT : 0 ≤ interpolationWeightBound n d := (interpolationWeightBound_pos n d).le
    unfold coefficientModulus
    exact mul_nonneg (mul_nonneg (coefficientExtractionBound_nonneg n d)
      (interpolationWeightBound_pos n d).le) (by positivity)

theorem coordinateBudget_pos (n d R : ℕ) : 0 < coordinateBudget n d R := by
  first
  | have hE := coefficientExtractionBound_nonneg n d
    have hC := coefficientModulus_nonneg n d R
    unfold coordinateBudget
    linarith

def netError (n d R k : ℕ) : ℚ :=
  (Fintype.card (MultiIndex n d) + 1) * coordinateBudget n d R * samplingTolerance k

def coefficientNet (n d R k : ℕ) : Finset (MultiIndex n d → ℚ) :=
  ((candidateTuples n d R (resolution n d k)).map
    (fun L => approximateCoefficients L (samplingTolerance k) (samplingTolerance_pos k))).toFinset

def boundedTarget (n d R : ℕ) : Set (QuadraticSeparation.Space (MultiIndex n d)) :=
  WithLp.toLp 2 '' boundedVolumeLocus n d
    (Icc (fun _ => -(R : ℝ)) (fun _ => (R : ℝ)))

theorem isCompact_boundedTarget (n d R : ℕ) : IsCompact (boundedTarget n d R) := by
  first
  | apply (isCompact_boundedVolumeLocus n d isCompact_Icc).image
    exact PiLp.continuous_toLp 2 _

theorem norm_le_sum_abs {ι : Type*} [Fintype ι] (x : QuadraticSeparation.Space ι) :
    ‖x‖ ≤ ∑ i, |x i| := by
  first
  | apply (sq_le_sq₀ (norm_nonneg x) (Finset.sum_nonneg fun i _ => abs_nonneg (x i))).mp
    rw [QuadraticSeparation.real_norm_sq_eq]
    simpa only [sq_abs] using
      (Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun i => |x i|)
        (fun i _ => abs_nonneg (x i)))

theorem dist_le_card_mul {ι : Type*} [Fintype ι] (x y : QuadraticSeparation.Space ι)
    {δ : ℝ} (h : ∀ i, |x i - y i| ≤ δ) : dist x y ≤ Fintype.card ι * δ := by
  first
  | rw [dist_eq_norm]
    apply (norm_le_sum_abs (x - y)).trans
    calc
      _ ≤ ∑ _i : ι, δ := Finset.sum_le_sum (fun i _ => h i)
      _ = Fintype.card ι * δ := by simp

theorem budget_to_netError {n d R k : ℕ}
    {x y : QuadraticSeparation.Space (MultiIndex n d)}
    (h : ∀ α, |x α - y α| ≤ (coordinateBudget n d R : ℝ) * (samplingTolerance k : ℝ)) :
    dist x y ≤ (netError n d R k : ℝ) := by
  first
  | apply (dist_le_card_mul x y h).trans
    simp only [netError, Rat.cast_mul, Rat.cast_add, Rat.cast_natCast, Rat.cast_one]
    have hB : 0 ≤ (coordinateBudget n d R : ℝ) := by
      exact_mod_cast (coordinateBudget_pos n d R).le
    have he : 0 ≤ (samplingTolerance k : ℝ) := by exact_mod_cast (samplingTolerance_pos k).le
    nlinarith

theorem coefficientNet_near (n d R k : ℕ) (q : MultiIndex n d → ℚ)
    (hq : q ∈ coefficientNet n d R k) :
    ∃ c ∈ boundedTarget n d R,
      dist (QuadraticSeparation.ofRat q) c ≤ (netError n d R k : ℝ) := by
  first
  | obtain ⟨L, hL, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    have hLi := (mem_candidateTuples L).mp hL
    have hL0 : ∀ i, 0 ∈ L i := fun i => ((mem_candidates (L i)).mp (hLi i)).2
    let K : Fin n → Body d := fun i => body (L i) (hL0 i)
    obtain ⟨c, hc⟩ := exists_volume_polynomial K
    refine ⟨WithLp.toLp 2 c, ⟨c, ⟨K, ?_, hc⟩, rfl⟩, ?_⟩
    · intro i
      exact ⟨zero_mem_body (L i) (hL0 i), candidate_bounded (L i) (hLi i)⟩
    · apply budget_to_netError
      intro α
      have ha := approximateCoefficients_correct L hL0 hc (samplingTolerance k)
        (samplingTolerance_pos k) α
      apply ha.trans
      apply mul_le_mul_of_nonneg_right _ (by exact_mod_cast (samplingTolerance_pos k).le)
      have hC : 0 ≤ (coefficientModulus n d (R : ℚ) : ℝ) := by
        exact_mod_cast coefficientModulus_nonneg n d R
      simp only [coordinateBudget, Rat.cast_add, Rat.cast_one]
      linarith

theorem coefficientNet_covers (n d R k : ℕ)
    (c : QuadraticSeparation.Space (MultiIndex n d)) (hc : c ∈ boundedTarget n d R) :
    ∃ q ∈ coefficientNet n d R k, dist c (QuadraticSeparation.ofRat q) ≤ (netError n d R k : ℝ) := by
  first
  | classical
    obtain ⟨c', ⟨K, hK, hc'⟩, rfl⟩ := hc
    choose L hL hdist using fun i => exists_candidate_near (R := R)
      (k := resolution n d k) (K i) (hK i).1 (hK i).2
    have hL0 : ∀ i, 0 ∈ L i := fun i => ((mem_candidates (L i)).mp (hL i)).2
    let P : Fin n → Body d := fun i => body (L i) (hL0 i)
    obtain ⟨cP, hcP⟩ := exists_volume_polynomial P
    let q := approximateCoefficients L (samplingTolerance k) (samplingTolerance_pos k)
    refine ⟨q, List.mem_toFinset.mpr (List.mem_map.mpr
      ⟨L, (mem_candidateTuples L).mpr hL, rfl⟩), ?_⟩
    apply budget_to_netError
    intro α
    have hgeom := hc'.coefficient_sub_le_of_dist_le hcP (R : ℚ) (by positivity)
      (fun i => (hK i).2) (fun i => candidate_bounded (L i) (hL i))
      (by positivity : 0 ≤ 1 / ((resolution n d k : ℝ) + 1))
      (resolution_bounds n d k).2 hdist α
    have happ := approximateCoefficients_correct L hL0 hcP (samplingTolerance k)
      (samplingTolerance_pos k) α
    have hC : 0 ≤ (coefficientModulus n d (R : ℚ) : ℝ) := by
      exact_mod_cast coefficientModulus_nonneg n d R
    have hgeom' : |c' α - cP α| ≤
        (samplingTolerance k : ℝ) * (coefficientModulus n d (R : ℚ) : ℝ) :=
      hgeom.trans (mul_le_mul_of_nonneg_right (resolution_bounds n d k).1 hC)
    have htri := abs_sub_le (c' α) (cP α) (q α : ℝ)
    rw [abs_sub_comm (cP α) (q α : ℝ)] at htri
    change |c' α - (q α : ℝ)| ≤ _
    have he : 0 ≤ (samplingTolerance k : ℝ) := by exact_mod_cast (samplingTolerance_pos k).le
    simp only [coordinateBudget, Rat.cast_add, Rat.cast_one]
    dsimp [q] at htri ⊢
    nlinarith

/-- The complete finite-net input, with its rational data executable and its
geometric meaning proved for actual compact convex bodies. -/
def model (n d R : ℕ) : QuadraticSeparation.Model (MultiIndex n d) where
  target := boundedTarget n d R
  closed := (isCompact_boundedTarget n d R).isClosed
  net := coefficientNet n d R
  error := netError n d R
  error_nonneg := by
    first
    | intro k
      exact mul_nonneg (mul_nonneg (by positivity) (coordinateBudget_pos n d R).le)
        (samplingTolerance_pos k).le
  error_tendsto := by
    first
    | have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
        (((Fintype.card (MultiIndex n d) : ℝ) + 1) * (coordinateBudget n d R : ℝ))
      simpa only [netError, samplingTolerance, Rat.cast_mul, Rat.cast_add, Rat.cast_div,
        Rat.cast_natCast, Rat.cast_one, mul_zero] using h
  net_near := coefficientNet_near n d R
  covers := coefficientNet_covers n d R

end VolumePolynomials.RationalCoefficientNets

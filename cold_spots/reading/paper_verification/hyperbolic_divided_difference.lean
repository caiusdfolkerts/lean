module
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
@[expose] public section
/-! # The positive divided-difference moment

This is the real one-dimensional version of the Hermite--Genocchi step in
Section 4.2.  The triangular density is integrated separately on its two
linear pieces, so no unproved simplex integration formula is required.
-/

noncomputable section

namespace PaperVerification.Hyperbolic

open Real Set MeasureTheory intervalIntegral

def dividedIntegral (v u : ℝ) (f : ℝ → ℝ) : ℝ :=
  (∫ s in v..u, (s - v) * f s) / ((u - v) * (1 - v)) +
    (∫ s in u..1, (1 - s) * f s) / ((1 - u) * (1 - v))

def powerDividedDifference (v u z : ℝ) : ℝ :=
  ((1 - u ^ z) / (1 - u) - (u ^ z - v ^ z) / (u - v)) / (1 - v)

def powerSecant (v u z : ℝ) : ℝ :=
  ((1 - v) * u ^ z - (1 - u) * v ^ z) / (u - v)

theorem dividedIntegral_congr {v u : ℝ} (hvu : v ≤ u) (hu : u ≤ 1)
    {f g : ℝ → ℝ} (h : ∀ s ∈ Icc v 1, f s = g s) :
    dividedIntegral v u f = dividedIntegral v u g := by
  unfold dividedIntegral
  congr 1
  · congr 1
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hvu]
    exact fun s hs => congrArg ((s - v) * ·) (h s ⟨hs.1, hs.2.trans hu⟩)
  · congr 1
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hu]
    exact fun s hs => congrArg ((1 - s) * ·) (h s ⟨hvu.trans hs.1, hs.2⟩)

theorem dividedIntegral_const_mul (v u c : ℝ) (f : ℝ → ℝ) :
    dividedIntegral v u (fun s => c * f s) = c * dividedIntegral v u f := by
  unfold dividedIntegral
  simp_rw [show ∀ s, (s - v) * (c * f s) = c * ((s - v) * f s) from fun s => by ring,
    show ∀ s, (1 - s) * (c * f s) = c * ((1 - s) * f s) from fun s => by ring]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring

theorem dividedIntegral_sub {v u : ℝ} (hv : 0 < v) (hvu : v < u) (hu : u < 1)
    {f g : ℝ → ℝ} (hf : ContinuousOn f (Icc v 1)) (hg : ContinuousOn g (Icc v 1)) :
    dividedIntegral v u (fun s => f s - g s) =
      dividedIntegral v u f - dividedIntegral v u g := by
  have hsub₁ : Icc v u ⊆ Icc v 1 := fun s hs => ⟨hs.1, hs.2.trans hu.le⟩
  have hsub₂ : Icc u 1 ⊆ Icc v 1 := fun s hs => ⟨hvu.le.trans hs.1, hs.2⟩
  have hfl : IntervalIntegrable (fun s => (s - v) * f s) volume v u :=
    ((continuousOn_id.sub continuousOn_const).mul (hf.mono hsub₁)).intervalIntegrable_of_Icc hvu.le
  have hgl : IntervalIntegrable (fun s => (s - v) * g s) volume v u :=
    ((continuousOn_id.sub continuousOn_const).mul (hg.mono hsub₁)).intervalIntegrable_of_Icc hvu.le
  have hfu : IntervalIntegrable (fun s => (1 - s) * f s) volume u 1 :=
    ((continuousOn_const.sub continuousOn_id).mul (hf.mono hsub₂)).intervalIntegrable_of_Icc hu.le
  have hgu : IntervalIntegrable (fun s => (1 - s) * g s) volume u 1 :=
    ((continuousOn_const.sub continuousOn_id).mul (hg.mono hsub₂)).intervalIntegrable_of_Icc hu.le
  unfold dividedIntegral
  simp_rw [mul_sub]
  rw [intervalIntegral.integral_sub hfl hgl, intervalIntegral.integral_sub hfu hgu]
  ring

theorem dividedIntegral_nonneg {v u : ℝ} (hv : 0 < v) (hvu : v < u) (hu : u < 1)
    {f : ℝ → ℝ} (hf : ∀ s ∈ Icc v 1, 0 ≤ f s) : 0 ≤ dividedIntegral v u f := by
  have hv1 := hvu.trans hu
  apply add_nonneg
  · apply div_nonneg _ (mul_pos (sub_pos.mpr hvu) (sub_pos.mpr hv1)).le
    apply intervalIntegral.integral_nonneg hvu.le
    intro s hs
    exact mul_nonneg (sub_nonneg.mpr hs.1) (hf s ⟨hs.1, hs.2.trans hu.le⟩)
  · apply div_nonneg _ (mul_pos (sub_pos.mpr hu) (sub_pos.mpr hv1)).le
    apply intervalIntegral.integral_nonneg hu.le
    intro s hs
    exact mul_nonneg (sub_nonneg.mpr hs.2) (hf s ⟨hvu.le.trans hs.1, hs.2⟩)

theorem continuousOn_rpow_positive_interval {a b z : ℝ} (ha : 0 < a) :
    ContinuousOn (fun s : ℝ => s ^ z) (Icc a b) :=
  continuousOn_id.rpow_const (fun s hs => Or.inl (ha.trans_le hs.1).ne')

theorem integral_linear_rpow_lower {v u z : ℝ} (hv : 0 < v) (hvu : v ≤ u) :
    (∫ s in v..u, (s - v) * (z * (z - 1) * s ^ (z - 2))) =
      (u - v) * z * u ^ (z - 1) - u ^ z + v ^ z := by
  let F : ℝ → ℝ := fun s => (s - v) * z * s ^ (z - 1) - s ^ z
  have hd : ∀ s ∈ uIcc v u,
      HasDerivAt F ((s - v) * (z * (z - 1) * s ^ (z - 2))) s := by
    rw [uIcc_of_le hvu]
    intro s hs
    have hs0 := hv.trans_le hs.1
    convert ((((hasDerivAt_id s).sub_const v).mul_const z).mul
      (Real.hasDerivAt_rpow_const (Or.inl hs0.ne') :
        HasDerivAt (fun s : ℝ => s ^ (z - 1)) ((z - 1) * s ^ ((z - 1) - 1)) s)).sub
      (Real.hasDerivAt_rpow_const (Or.inl hs0.ne') :
        HasDerivAt (fun s : ℝ => s ^ z) (z * s ^ (z - 1)) s) using 1
    · rfl
    · rw [show z - 1 - 1 = z - 2 by ring]
      simp only [Pi.sub_apply, Pi.mul_apply, id_eq]
      ring
  have hc : ContinuousOn (fun s : ℝ => (s - v) * (z * (z - 1) * s ^ (z - 2))) (Icc v u) :=
    (continuousOn_id.sub continuousOn_const).mul
      (continuousOn_const.mul (continuousOn_rpow_positive_interval hv))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable_of_Icc hvu)
  simpa only [F, sub_self, zero_mul, zero_sub, sub_neg_eq_add] using h

theorem integral_linear_rpow_upper {u z : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    (∫ s in u..1, (1 - s) * (z * (z - 1) * s ^ (z - 2))) =
      -(1 - u) * z * u ^ (z - 1) + 1 - u ^ z := by
  let F : ℝ → ℝ := fun s => (1 - s) * z * s ^ (z - 1) + s ^ z
  have hd : ∀ s ∈ uIcc u 1,
      HasDerivAt F ((1 - s) * (z * (z - 1) * s ^ (z - 2))) s := by
    rw [uIcc_of_le hu1]
    intro s hs
    have hs0 := hu0.trans_le hs.1
    convert ((((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s)).mul_const z).mul
      (Real.hasDerivAt_rpow_const (Or.inl hs0.ne') :
        HasDerivAt (fun s : ℝ => s ^ (z - 1)) ((z - 1) * s ^ ((z - 1) - 1)) s)).add
      (Real.hasDerivAt_rpow_const (Or.inl hs0.ne') :
        HasDerivAt (fun s : ℝ => s ^ z) (z * s ^ (z - 1)) s) using 1
    · rfl
    · rw [show z - 1 - 1 = z - 2 by ring]
      simp only [Pi.sub_apply, Pi.mul_apply, id_eq]
      ring
  have hc : ContinuousOn (fun s : ℝ => (1 - s) * (z * (z - 1) * s ^ (z - 2))) (Icc u 1) :=
    (continuousOn_const.sub continuousOn_id).mul
      (continuousOn_const.mul (continuousOn_rpow_positive_interval hu0))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable_of_Icc hu1)
  simp only [F, sub_self, zero_mul, zero_add, Real.one_rpow] at h
  linarith

/-- The precise power instance of the Hermite--Genocchi formula. -/
theorem powerDividedDifference_eq_integral {v u z : ℝ}
    (hv : 0 < v) (hvu : v < u) (hu : u < 1) :
    powerDividedDifference v u z =
      z * (z - 1) * dividedIntegral v u (fun s => s ^ (z - 2)) := by
  rw [← dividedIntegral_const_mul]
  unfold dividedIntegral
  rw [integral_linear_rpow_lower hv hvu.le,
    integral_linear_rpow_upper (hv.trans hvu) hu.le]
  unfold powerDividedDifference
  field_simp [(sub_pos.mpr hvu).ne', (sub_pos.mpr hu).ne', (sub_pos.mpr (hvu.trans hu)).ne'] <;> ring

/-- Reciprocal substitution about the geometric mean of two positive endpoints. -/
theorem integral_reciprocal_geometric {v u g : ℝ}
    (hv : 0 < v) (hvu : v < u) (hg : 0 < g) (hg2 : g ^ 2 = v * u)
    (hvg : v ≤ g) (hgu : g ≤ u) (f : ℝ → ℝ) :
    (∫ s in g..u, f (g ^ 2 / s) * (g ^ 2 / s ^ 2)) = ∫ s in v..g, f s := by
  have hnz : ∀ s ∈ uIcc g u, s ≠ 0 := by
    rw [uIcc_of_le hgu]
    exact fun s hs => (hg.trans_le hs.1).ne'
  have hc : ContinuousOn (fun s : ℝ => g ^ 2 / s) (uIcc g u) :=
    continuousOn_const.div continuousOn_id hnz
  have hd : ∀ s ∈ Ioo (min g u) (max g u),
      HasDerivAt (fun s : ℝ => g ^ 2 / s) (-(g ^ 2 / s ^ 2)) s := by
    intro s hs
    have hs0 : s ≠ 0 := by
      rw [min_eq_left hgu, max_eq_right hgu] at hs
      exact (hg.trans hs.1).ne'
    convert (hasDerivAt_inv hs0).const_mul (g ^ 2) using 1 <;>
      (try funext s) <;> (try simp only [one_div, div_eq_mul_inv]) <;> ring
  have hm : ∀ s ∈ Ioo (min g u) (max g u), -(g ^ 2 / s ^ 2) ≤ 0 :=
    fun s _ => neg_nonpos.mpr (div_nonneg (sq_nonneg g) (sq_nonneg s))
  have h := integral_comp_mul_deriv_of_deriv_nonpos (g := f) hc hd hm
  have hleft : g ^ 2 / g = g := by field_simp [hg.ne']
  have hright : g ^ 2 / u = v := by rw [hg2]; field_simp [(hv.trans hvu).ne']
  have hfun : (fun s : ℝ => (f ∘ fun s => g ^ 2 / s) s * -(g ^ 2 / s ^ 2)) =
      fun s => -(f (g ^ 2 / s) * (g ^ 2 / s ^ 2)) := by
    funext s
    simp only [Function.comp_apply]
    ring
  rw [hfun, intervalIntegral.integral_neg, hleft, hright, intervalIntegral.integral_symm v g] at h
  exact neg_injective h

theorem dividedIntegral_geometric_base_pos {v u g : ℝ}
    (hv : 0 < v) (hvu : v < u) (hu : u < 1)
    (hg : 0 < g) (hg2 : g ^ 2 = v * u) (hvg : v < g) (hgu : g < u) :
    0 < dividedIntegral v u (fun s => (s - g) / s ^ 2) := by
  let f : ℝ → ℝ := fun s => (s - v) * ((s - g) / s ^ 2)
  have hf : ContinuousOn f (Icc v u) := by
    exact (continuousOn_id.sub continuousOn_const).mul
      ((continuousOn_id.sub continuousOn_const).div (continuousOn_id.pow 2)
        (fun s hs => pow_ne_zero 2 (hv.trans_le hs.1).ne'))
  have hfg : IntervalIntegrable f volume v g :=
    (hf.mono (fun s hs => ⟨hs.1, hs.2.trans hgu.le⟩)).intervalIntegrable_of_Icc hvg.le
  have hfu : IntervalIntegrable f volume g u :=
    (hf.mono (fun s hs => ⟨hvg.le.trans hs.1, hs.2⟩)).intervalIntegrable_of_Icc hgu.le
  have hrec : ContinuousOn (fun s => f (g ^ 2 / s) * (g ^ 2 / s ^ 2)) (Icc g u) := by
    have hq : ContinuousOn (fun s : ℝ => g ^ 2 / s) (Icc g u) :=
      continuousOn_const.div continuousOn_id (fun s hs => (hg.trans_le hs.1).ne')
    exact ((hq.sub continuousOn_const).mul
      ((hq.sub continuousOn_const).div (hq.pow 2)
        (fun s hs => pow_ne_zero 2 (div_ne_zero (pow_ne_zero 2 hg.ne') (hg.trans_le hs.1).ne')))).mul
      (continuousOn_const.div (continuousOn_id.pow 2)
        (fun s hs => pow_ne_zero 2 (hg.trans_le hs.1).ne'))
  have hpair : ∀ s ∈ Icc g u,
      f s + f (g ^ 2 / s) * (g ^ 2 / s ^ 2) =
        (1 + v / g) * (s - g) ^ 2 / s ^ 2 := by
    intro s hs
    dsimp [f]
    field_simp [hg.ne', (hg.trans_le hs.1).ne'] <;> ring
  have hlow : 0 ≤ ∫ s in v..u, f s := by
    rw [← integral_add_adjacent_intervals hfg hfu,
      ← integral_reciprocal_geometric hv hvu hg hg2 hvg.le hgu.le f, add_comm,
      ← intervalIntegral.integral_add hfu (hrec.intervalIntegrable_of_Icc hgu.le)]
    apply intervalIntegral.integral_nonneg hgu.le
    intro s hs
    rw [hpair s hs]
    exact div_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) (sq_nonneg s)
  have hu0 := hv.trans hvu
  have hupp : 0 < ∫ s in u..1, (1 - s) * ((s - g) / s ^ 2) := by
    apply intervalIntegral.integral_pos hu
    · exact (continuousOn_const.sub continuousOn_id).mul
        ((continuousOn_id.sub continuousOn_const).div (continuousOn_id.pow 2)
          (fun s hs => pow_ne_zero 2 (hu0.trans_le hs.1).ne'))
    · intro s hs
      exact mul_nonneg (sub_nonneg.mpr hs.2)
        (div_nonneg (sub_nonneg.mpr (hgu.le.trans hs.1.le)) (sq_nonneg s))
    · let m := (u + 1) / 2
      have hm : m ∈ Ioo u 1 := by dsimp [m]; constructor <;> linarith
      exact ⟨m, ⟨hm.1.le, hm.2.le⟩, mul_pos (sub_pos.mpr hm.2)
        (div_pos (sub_pos.mpr (hgu.trans hm.1)) (sq_pos_of_ne_zero (hu0.trans hm.1).ne'))⟩
  exact add_pos_of_nonneg_of_pos
    (div_nonneg hlow (mul_pos (sub_pos.mpr hvu) (sub_pos.mpr (hvu.trans hu))).le)
    (div_pos hupp (mul_pos (sub_pos.mpr hu) (sub_pos.mpr (hvu.trans hu))))

/-- Strict positivity of equation (17), throughout its full exponent range. -/
theorem dividedIntegral_geometric_rpow_pos {v u r : ℝ}
    (hv : 0 < v) (hvu : v < u) (hu : u < 1) (hr : 0 ≤ r) :
    0 < dividedIntegral v u (fun s => (s - Real.sqrt (v * u)) * s ^ (r - 2)) := by
  let g := Real.sqrt (v * u)
  have hu0 := hv.trans hvu
  have hg : 0 < g := Real.sqrt_pos.mpr (mul_pos hv hu0)
  have hg2 : g ^ 2 = v * u := Real.sq_sqrt (mul_nonneg hv.le hu0.le)
  have hvg : v < g := by nlinarith only [hg2, hv, hg, mul_lt_mul_of_pos_left hvu hv]
  have hgu : g < u := by nlinarith only [hg2, hu0, hg, mul_lt_mul_of_pos_right hvu hu0]
  have hbase := dividedIntegral_geometric_base_pos hv hvu hu hg hg2 hvg hgu
  let f : ℝ → ℝ := fun s => (s - g) * s ^ (r - 2)
  let f₀ : ℝ → ℝ := fun s => (s - g) / s ^ 2
  have hf : ContinuousOn f (Icc v 1) :=
    (continuousOn_id.sub continuousOn_const).mul (continuousOn_rpow_positive_interval hv)
  have hf₀ : ContinuousOn f₀ (Icc v 1) :=
    (continuousOn_id.sub continuousOn_const).div (continuousOn_id.pow 2)
      (fun s hs => pow_ne_zero _ (hv.trans_le hs.1).ne')
  have hgf₀ : ContinuousOn (fun s => g ^ r * f₀ s) (Icc v 1) := continuousOn_const.mul hf₀
  have hdiff : 0 ≤ dividedIntegral v u (fun s => f s - g ^ r * f₀ s) := by
    apply dividedIntegral_nonneg hv hvu hu
    intro s hs
    have hs0 := hv.trans_le hs.1
    have hp : 0 ≤ (s - g) * (s ^ r - g ^ r) := by
      rcases le_total g s with h | h
      · exact mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr (Real.rpow_le_rpow hg.le h hr))
      · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h)
          (sub_nonpos.mpr (Real.rpow_le_rpow hs0.le h hr))
    dsimp [f, f₀]
    rw [Real.rpow_sub hs0 r 2, Real.rpow_ofNat]
    have he : (s - g) * (s ^ r / s ^ 2) - g ^ r * ((s - g) / s ^ 2) =
        ((s - g) * (s ^ r - g ^ r)) / s ^ 2 := by ring
    rw [he]
    exact div_nonneg hp (sq_nonneg s)
  rw [dividedIntegral_sub hv hvu hu hf hgf₀,
    dividedIntegral_const_mul] at hdiff
  have hmul : 0 < g ^ r * dividedIntegral v u f₀ :=
    mul_pos (Real.rpow_pos_of_pos hg _) hbase
  change 0 < dividedIntegral v u f
  linarith

theorem powerSecant_sub_one {v u z : ℝ} (hvu : v < u) (hu : u < 1) :
    powerSecant v u z - 1 = -(1 - u) * (1 - v) * powerDividedDifference v u z := by
  unfold powerSecant powerDividedDifference
  field_simp [(sub_pos.mpr hvu).ne', (sub_pos.mpr hu).ne', (sub_pos.mpr (hvu.trans hu)).ne'] <;> ring

/-- The strict algebraic form of equation (16). -/
theorem powerSecant_geometric_inequality {v u r : ℝ}
    (hv : 0 < v) (hvu : v < u) (hu : u < 1) (hr : r ∈ Ioo 0 1) :
    (1 + r) * Real.sqrt (v * u) * (powerSecant v u r - 1) +
      (1 - r) * (powerSecant v u (1 + r) - 1) < 0 := by
  let g := Real.sqrt (v * u)
  let J := dividedIntegral v u (fun s => (s - g) * s ^ (r - 2))
  have hJ : 0 < J := dividedIntegral_geometric_rpow_pos hv hvu hu hr.1.le
  have hmoment : J = dividedIntegral v u (fun s => s ^ (r - 1)) -
      g * dividedIntegral v u (fun s => s ^ (r - 2)) := by
    have hf : ContinuousOn (fun s : ℝ => s ^ (r - 1)) (Icc v 1) := continuousOn_rpow_positive_interval hv
    have hg : ContinuousOn (fun s : ℝ => g * s ^ (r - 2)) (Icc v 1) :=
      continuousOn_const.mul (continuousOn_rpow_positive_interval hv)
    rw [← dividedIntegral_const_mul, ← dividedIntegral_sub hv hvu hu hf hg]
    apply dividedIntegral_congr hvu.le hu.le
    intro s hs
    have hs0 := hv.trans_le hs.1
    have hpow : s ^ (r - 1) = s ^ (r - 2) * s := by
      convert Real.rpow_add_one hs0.ne' (r - 2) using 1 <;> congr 1 <;> ring
    rw [hpow]
    ring
  rw [powerSecant_sub_one hvu hu, powerSecant_sub_one hvu hu,
    powerDividedDifference_eq_integral hv hvu hu,
    powerDividedDifference_eq_integral hv hvu hu]
  rw [show 1 + r - 2 = r - 1 by ring]
  have he : (1 + r) * Real.sqrt (v * u) *
      (-(1 - u) * (1 - v) * (r * (r - 1) * dividedIntegral v u (fun s => s ^ (r - 2)))) +
      (1 - r) * (-(1 - u) * (1 - v) *
        ((1 + r) * (1 + r - 1) * dividedIntegral v u (fun s => s ^ (r - 1)))) =
      -((1 - u) * (1 - v) * r * (1 - r) * (1 + r)) * J := by
    rw [hmoment]
    dsimp [g]
    ring
  rw [he]
  apply mul_neg_of_neg_of_pos _ hJ
  apply neg_neg_of_pos
  exact mul_pos (mul_pos (mul_pos (mul_pos (sub_pos.mpr hu)
    (sub_pos.mpr (hvu.trans hu))) hr.1) (sub_pos.mpr hr.2)) (by linarith [hr.1])

end PaperVerification.Hyperbolic

#print axioms PaperVerification.Hyperbolic.powerDividedDifference_eq_integral
#print axioms PaperVerification.Hyperbolic.dividedIntegral_geometric_rpow_pos

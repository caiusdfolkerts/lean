module
public import PaperVerification.HyperbolicDividedDifference
public import PaperVerification.HyperbolicJensen
public import PaperVerification.HyperbolicTwoPoint
@[expose] public section
/-! # The translated arithmetic deficits

Both functions are the literal real-power expressions in Section 4.2.
The derivative calculation is reduced to the already proved positive
divided-difference moment.
-/

noncomputable section

namespace PaperVerification.Hyperbolic

open Real Set

def arithmeticDeficit (δ r a : ℝ) : ℝ :=
  Real.cosh a ^ (2 + 2 * r) * Real.cosh (a + δ) ^ (2 - 2 * r) -
    Real.sinh a ^ (2 + 2 * r) * Real.sinh (a + δ) ^ (2 - 2 * r) -
    (1 + r) / 2 * Real.cosh (2 * a) - (1 - r) / 2 * Real.cosh (2 * (a + δ))

theorem rpow_weighted_square_ratio {x y r : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x ^ (2 + 2 * r) * y ^ (2 - 2 * r) =
      x ^ 2 * y ^ 2 * (x ^ 2 / y ^ 2) ^ r := by
  have hx' : (x ^ 2) ^ r = x ^ (2 * r) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hx.le]
  have hy' : (y ^ 2) ^ r = y ^ (2 * r) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hy.le]
  rw [Real.rpow_add hx 2 (2 * r), Real.rpow_sub hy 2 (2 * r),
    Real.rpow_two, Real.rpow_two, Real.div_rpow (sq_nonneg x) (sq_nonneg y), hx', hy']
  ring

theorem hasDerivAt_rpow_product_logarithmic {f g : ℝ → ℝ} {x f' g' r s : ℝ}
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x)
    (hfx : 0 < f x) (hgx : 0 < g x) :
    HasDerivAt (fun y => f y ^ r * g y ^ s)
      (f x ^ r * g x ^ s * (r * f' / f x + s * g' / g x)) x := by
  convert (hf.rpow_const (Or.inl hfx.ne')).mul (hg.rpow_const (Or.inl hgx.ne')) using 1
  rw [Real.rpow_sub_one hfx.ne' r, Real.rpow_sub_one hgx.ne' s]
  field_simp [hfx.ne', hgx.ne'] <;> ring

theorem powerSecant_eq_linear {v u D T z : ℝ} (hvu : v ≠ u)
    (h₁ : D ^ 2 - T ^ 2 = 1) (h₂ : D ^ 2 * u - T ^ 2 * v = 1) :
    powerSecant v u z = D ^ 2 * u ^ z - T ^ 2 * v ^ z := by
  have hD : (u - v) * D ^ 2 = 1 - v := by linear_combination h₂ - v * h₁
  have hT : (u - v) * T ^ 2 = 1 - u := by linear_combination h₂ - u * h₁
  unfold powerSecant
  rw [← hD, ← hT]
  field_simp [sub_ne_zero.mpr hvu.symm] <;> ring

theorem hyperbolic_square_ratio_bounds {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    0 < Real.sinh a ^ 2 / Real.sinh (a + δ) ^ 2 ∧
      Real.sinh a ^ 2 / Real.sinh (a + δ) ^ 2 <
        Real.cosh a ^ 2 / Real.cosh (a + δ) ^ 2 ∧
      Real.cosh a ^ 2 / Real.cosh (a + δ) ^ 2 < 1 := by
  have hb : 0 < a + δ := add_pos ha hδ
  have hab : a < a + δ := lt_add_of_pos_right _ hδ
  have hC := Real.cosh_pos a
  have hD := Real.cosh_pos (a + δ)
  have hS := Real.sinh_pos_iff.mpr ha
  have hT := Real.sinh_pos_iff.mpr hb
  have hCD : Real.cosh a < Real.cosh (a + δ) := Real.cosh_strictMonoOn ha.le hb.le hab
  have hST : Real.sinh a < Real.sinh (a + δ) := Real.sinh_strictMono hab
  have hCs : Real.cosh a ^ 2 = 1 + Real.sinh a ^ 2 := by linarith [Real.cosh_sq_sub_sinh_sq a]
  have hDs : Real.cosh (a + δ) ^ 2 = 1 + Real.sinh (a + δ) ^ 2 := by
    linarith [Real.cosh_sq_sub_sinh_sq (a + δ)]
  refine ⟨div_pos (sq_pos_of_ne_zero hS.ne') (sq_pos_of_ne_zero hT.ne'), ?_, ?_⟩
  · apply (div_lt_div_iff₀ (sq_pos_of_ne_zero hT.ne') (sq_pos_of_ne_zero hD.ne')).mpr
    rw [hCs, hDs]
    nlinarith only [(sq_lt_sq₀ hS.le hT.le).mpr hST]
  · apply (div_lt_one (sq_pos_of_ne_zero hD.ne')).mpr
    exact (sq_lt_sq₀ hC.le hD.le).mpr hCD

theorem hasDerivAt_arithmeticDeficit {a δ r : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    HasDerivAt (arithmeticDeficit δ r)
      (2 * ((1 + r) * Real.cosh a * Real.sinh a *
          (powerSecant (Real.sinh a ^ 2 / Real.sinh (a + δ) ^ 2)
            (Real.cosh a ^ 2 / Real.cosh (a + δ) ^ 2) r - 1) +
        (1 - r) * Real.cosh (a + δ) * Real.sinh (a + δ) *
          (powerSecant (Real.sinh a ^ 2 / Real.sinh (a + δ) ^ 2)
            (Real.cosh a ^ 2 / Real.cosh (a + δ) ^ 2) (1 + r) - 1))) a := by
  let C := Real.cosh a
  let S := Real.sinh a
  let D := Real.cosh (a + δ)
  let T := Real.sinh (a + δ)
  let u := C ^ 2 / D ^ 2
  let v := S ^ 2 / T ^ 2
  have hC : 0 < C := Real.cosh_pos _
  have hD : 0 < D := Real.cosh_pos _
  have hS : 0 < S := Real.sinh_pos_iff.mpr ha
  have hT : 0 < T := Real.sinh_pos_iff.mpr (add_pos ha hδ)
  obtain ⟨hv, hvu, hu⟩ := hyperbolic_square_ratio_bounds ha hδ
  change 0 < v at hv
  change v < u at hvu
  change u < 1 at hu
  have hu0 := hv.trans hvu
  have hu' : D ^ 2 * u = C ^ 2 := by dsimp [u]; field_simp [hD.ne']
  have hv' : T ^ 2 * v = S ^ 2 := by dsimp [v]; field_simp [hT.ne']
  have h₁ : D ^ 2 - T ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq _
  have h₂ : D ^ 2 * u - T ^ 2 * v = 1 := by rw [hu', hv']; exact Real.cosh_sq_sub_sinh_sq _
  have hφ (z : ℝ) : powerSecant v u z = D ^ 2 * u ^ z - T ^ 2 * v ^ z :=
    powerSecant_eq_linear hvu.ne h₁ h₂
  have hφ' : powerSecant v u (1 + r) = C ^ 2 * u ^ r - S ^ 2 * v ^ r := by
    rw [hφ, Real.rpow_add hu0 1 r, Real.rpow_add hv 1 r, Real.rpow_one, Real.rpow_one]
    rw [← mul_assoc, hu', ← mul_assoc, hv']
  have hDb : HasDerivAt (fun a => Real.cosh (a + δ)) T a := by
    simpa only [mul_one, id_eq, T] using ((hasDerivAt_id a).add_const δ).cosh
  have hTb : HasDerivAt (fun a => Real.sinh (a + δ)) D a := by
    simpa only [mul_one, id_eq, D] using ((hasDerivAt_id a).add_const δ).sinh
  have hprodC := hasDerivAt_rpow_product_logarithmic (r := 2 + 2 * r) (s := 2 - 2 * r)
    (Real.hasDerivAt_cosh a) hDb hC hD
  have hprodS := hasDerivAt_rpow_product_logarithmic (r := 2 + 2 * r) (s := 2 - 2 * r)
    (Real.hasDerivAt_sinh a) hTb hS hT
  have hd := ((hprodC.sub hprodS).sub
    ((((hasDerivAt_id a).const_mul 2).cosh).const_mul ((1 + r) / 2))).sub
    (((((hasDerivAt_id a).add_const δ).const_mul 2).cosh).const_mul ((1 - r) / 2))
  convert hd using 1
  · rfl
  · change 2 * ((1 + r) * C * S * (powerSecant v u r - 1) +
        (1 - r) * D * T * (powerSecant v u (1 + r) - 1)) = _
    rw [hφ', hφ, rpow_weighted_square_ratio hC hD, rpow_weighted_square_ratio hS hT]
    simp only [Real.sinh_two_mul, mul_one]
    change 2 * ((1 + r) * C * S * (D ^ 2 * u ^ r - T ^ 2 * v ^ r - 1) +
      (1 - r) * D * T * (C ^ 2 * u ^ r - S ^ 2 * v ^ r - 1)) =
      C ^ 2 * D ^ 2 * u ^ r * ((2 + 2 * r) * S / C + (2 - 2 * r) * T / D) -
        S ^ 2 * T ^ 2 * v ^ r * ((2 + 2 * r) * C / S + (2 - 2 * r) * D / T) -
        (1 + r) / 2 * (2 * S * C * 2) -
        (1 - r) / 2 * (2 * T * D * 2)
    field_simp [hC.ne', hD.ne', hS.ne', hT.ne'] <;> ring

theorem deriv_arithmeticDeficit_neg {a δ r : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hr : r ∈ Ioo 0 1) :
    deriv (arithmeticDeficit δ r) a < 0 := by
  let C := Real.cosh a
  let S := Real.sinh a
  let D := Real.cosh (a + δ)
  let T := Real.sinh (a + δ)
  let u := C ^ 2 / D ^ 2
  let v := S ^ 2 / T ^ 2
  have hC : 0 < C := Real.cosh_pos _
  have hD : 0 < D := Real.cosh_pos _
  have hS : 0 < S := Real.sinh_pos_iff.mpr ha
  have hT : 0 < T := Real.sinh_pos_iff.mpr (add_pos ha hδ)
  obtain ⟨hv, hvu, hu⟩ := hyperbolic_square_ratio_bounds ha hδ
  change 0 < v at hv
  change v < u at hvu
  change u < 1 at hu
  have harg : v * u = (C * S / (D * T)) ^ 2 := by
    dsimp [v, u]
    field_simp [hD.ne', hT.ne'] <;> ring
  have hg : Real.sqrt (v * u) = C * S / (D * T) := by
    rw [harg, Real.sqrt_sq_eq_abs, abs_of_pos (div_pos (mul_pos hC hS) (mul_pos hD hT))]
  have hineg := powerSecant_geometric_inequality hv hvu hu hr
  have hneg := mul_neg_of_pos_of_neg (mul_pos (by norm_num : (0 : ℝ) < 2) (mul_pos hD hT)) hineg
  rw [(hasDerivAt_arithmeticDeficit ha hδ).deriv]
  change 2 * ((1 + r) * C * S * (powerSecant v u r - 1) +
    (1 - r) * D * T * (powerSecant v u (1 + r) - 1)) < 0
  rw [hg] at hneg
  convert hneg using 1 <;> field_simp [hD.ne', hT.ne'] <;> ring

theorem continuous_arithmeticDeficit {δ r : ℝ} (hr : r ∈ Ioo (-1) 1) :
    Continuous (arithmeticDeficit δ r) := by
  have hplus : 0 ≤ 2 + 2 * r := by linarith [hr.1]
  have hminus : 0 ≤ 2 - 2 * r := by linarith [hr.2]
  unfold arithmeticDeficit
  exact (((Real.continuous_cosh.rpow_const (fun _ => Or.inr hplus)).mul
    ((Real.continuous_cosh.comp (continuous_id.add continuous_const)).rpow_const
      (fun _ => Or.inr hminus))).sub
    ((Real.continuous_sinh.rpow_const (fun _ => Or.inr hplus)).mul
      ((Real.continuous_sinh.comp (continuous_id.add continuous_const)).rpow_const
        (fun _ => Or.inr hminus)))).sub
    (continuous_const.mul (Real.continuous_cosh.comp (continuous_const.mul continuous_id))) |>.sub
    (continuous_const.mul (Real.continuous_cosh.comp
      (continuous_const.mul (continuous_id.add continuous_const))))

/-- The strict decrease asserted in equation (15), including the endpoint. -/
theorem strictAntiOn_arithmeticDeficit {δ r : ℝ} (hδ : 0 < δ) (hr : r ∈ Ioo 0 1) :
    StrictAntiOn (arithmeticDeficit δ r) (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 0)
    (continuous_arithmeticDeficit ⟨by linarith [hr.1], hr.2⟩).continuousOn
  intro a ha
  have ha0 : 0 < a := by simpa only [interior_Ici, mem_Ioi] using ha
  exact deriv_arithmeticDeficit_neg ha0 hδ hr

theorem rpow_symmetric_eq_sinh {x : ℝ} (hx : 0 < x) (r : ℝ) :
    x ^ r + x ^ (-r) = 4 * Real.sinh (r * Real.log x / 2) ^ 2 + 2 := by
  let t := r * Real.log x / 2
  have he : x ^ r + x ^ (-r) = 2 * Real.cosh (2 * t) := by
    rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hx, Real.cosh_eq]
    have h₁ : Real.log x * r = 2 * t := by dsimp [t]; ring
    have h₂ : Real.log x * (-r) = -(2 * t) := by dsimp [t]; ring
    rw [h₁, h₂]
    ring
  rw [he, Real.cosh_two_mul]
  nlinarith only [Real.cosh_sq_sub_sinh_sq t]

theorem rpow_square_ratio_symmetric {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (r : ℝ) :
    (x ^ 2 / y ^ 2) ^ r + (x ^ 2 / y ^ 2) ^ (-r) =
      4 * Real.sinh (r * Real.log (y / x)) ^ 2 + 2 := by
  rw [rpow_symmetric_eq_sinh (div_pos (sq_pos_of_ne_zero hx.ne') (sq_pos_of_ne_zero hy.ne'))]
  have ha : r * Real.log (x ^ 2 / y ^ 2) / 2 = -(r * Real.log (y / x)) := by
    rw [Real.log_div (pow_ne_zero _ hx.ne') (pow_ne_zero _ hy.ne'),
      Real.log_pow, Real.log_pow, Real.log_div hy.ne' hx.ne']
    norm_num
    ring
  rw [ha, Real.sinh_neg, neg_sq]

theorem sinh_log_ratio_balance {C S D T : ℝ}
    (hC : 0 < C) (hS : 0 < S) (hD : 0 < D) (hT : 0 < T)
    (h₁ : C ^ 2 - S ^ 2 = 1) (h₂ : D ^ 2 - T ^ 2 = 1) :
    C * D * Real.sinh (Real.log (D / C)) =
      S * T * Real.sinh (Real.log (T / S)) := by
  have hleft : C * D * Real.sinh (Real.log (D / C)) = (D ^ 2 - C ^ 2) / 2 := by
    rw [Real.sinh_eq, Real.exp_log (div_pos hD hC), Real.exp_neg,
      Real.exp_log (div_pos hD hC)]
    field_simp [hC.ne', hD.ne'] <;> ring
  have hright : S * T * Real.sinh (Real.log (T / S)) = (T ^ 2 - S ^ 2) / 2 := by
    rw [Real.sinh_eq, Real.exp_log (div_pos hT hS), Real.exp_neg,
      Real.exp_log (div_pos hT hS)]
    field_simp [hS.ne', hT.ne'] <;> ring
  rw [hleft, hright]
  linarith

theorem arithmeticDeficit_sum_identity {a δ r : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    arithmeticDeficit δ r a + arithmeticDeficit δ (-r) a =
      4 * ((Real.cosh a * Real.cosh (a + δ) *
          Real.sinh (r * Real.log (Real.cosh (a + δ) / Real.cosh a))) ^ 2 -
        (Real.sinh a * Real.sinh (a + δ) *
          Real.sinh (r * Real.log (Real.sinh (a + δ) / Real.sinh a))) ^ 2) := by
  have hC := Real.cosh_pos a
  have hD := Real.cosh_pos (a + δ)
  have hS := Real.sinh_pos_iff.mpr ha
  have hT := Real.sinh_pos_iff.mpr (add_pos ha hδ)
  have hbase : 2 * (Real.cosh a ^ 2 * Real.cosh (a + δ) ^ 2 -
      Real.sinh a ^ 2 * Real.sinh (a + δ) ^ 2) =
        Real.cosh (2 * a) + Real.cosh (2 * (a + δ)) := by
    rw [Real.cosh_two_mul, Real.cosh_two_mul]
    linear_combination
      (Real.cosh (a + δ) ^ 2 + Real.sinh (a + δ) ^ 2) * Real.cosh_sq_sub_sinh_sq a +
      (Real.cosh a ^ 2 + Real.sinh a ^ 2) * Real.cosh_sq_sub_sinh_sq (a + δ)
  unfold arithmeticDeficit
  rw [rpow_weighted_square_ratio hC hD, rpow_weighted_square_ratio hS hT,
    rpow_weighted_square_ratio hC hD, rpow_weighted_square_ratio hS hT]
  calc
    _ = Real.cosh a ^ 2 * Real.cosh (a + δ) ^ 2 *
        ((Real.cosh a ^ 2 / Real.cosh (a + δ) ^ 2) ^ r +
          (Real.cosh a ^ 2 / Real.cosh (a + δ) ^ 2) ^ (-r)) -
      Real.sinh a ^ 2 * Real.sinh (a + δ) ^ 2 *
        ((Real.sinh a ^ 2 / Real.sinh (a + δ) ^ 2) ^ r +
          (Real.sinh a ^ 2 / Real.sinh (a + δ) ^ 2) ^ (-r)) -
      Real.cosh (2 * a) - Real.cosh (2 * (a + δ)) := by ring
    _ = _ := by
      rw [rpow_square_ratio_symmetric hC hD, rpow_square_ratio_symmetric hS hT]
      linear_combination hbase

theorem arithmeticDeficit_sum_pos_of_pos {a δ r : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hr : r ∈ Ioo 0 1) :
    0 < arithmeticDeficit δ r a + arithmeticDeficit δ (-r) a := by
  let C := Real.cosh a
  let S := Real.sinh a
  let D := Real.cosh (a + δ)
  let T := Real.sinh (a + δ)
  let A := Real.log (D / C)
  let B := Real.log (T / S)
  have hC : 0 < C := Real.cosh_pos _
  have hD : 0 < D := Real.cosh_pos _
  have hS : 0 < S := Real.sinh_pos_iff.mpr ha
  have hT : 0 < T := Real.sinh_pos_iff.mpr (add_pos ha hδ)
  have hab : a < a + δ := lt_add_of_pos_right _ hδ
  have hCD : C < D := Real.cosh_strictMonoOn ha.le (add_pos ha hδ).le hab
  have hA : 0 < A := Real.log_pos ((one_lt_div hC).mpr hCD)
  have hTC : 0 < T * C - D * S := by
    have hs := Real.sinh_sub (a + δ) a
    rw [add_sub_cancel_left] at hs
    rw [← hs]
    exact Real.sinh_pos_iff.mpr hδ
  have hAB : A < B := Real.log_lt_log (div_pos hD hC)
    ((div_lt_div_iff₀ hC hS).mpr (by linarith only [hTC]))
  have hB := hA.trans hAB
  have hbalance : C * D * Real.sinh A = S * T * Real.sinh B :=
    sinh_log_ratio_balance hC hS hD hT (Real.cosh_sq_sub_sinh_sq _) (Real.cosh_sq_sub_sinh_sq _)
  have hratio := strictAntiOn_sinh_scale_ratio hr hA hB hAB
  have hprod : S * T * Real.sinh (r * B) < C * D * Real.sinh (r * A) := by
    calc
      _ = (C * D * Real.sinh A) * (Real.sinh (r * B) / Real.sinh B) := by
        rw [hbalance]
        field_simp [(Real.sinh_pos_iff.mpr hB).ne'] <;> ring
      _ < (C * D * Real.sinh A) * (Real.sinh (r * A) / Real.sinh A) :=
        mul_lt_mul_of_pos_left hratio (mul_pos (mul_pos hC hD) (Real.sinh_pos_iff.mpr hA))
      _ = _ := by field_simp [(Real.sinh_pos_iff.mpr hA).ne'] <;> ring
  have hsquare : (S * T * Real.sinh (r * B)) ^ 2 < (C * D * Real.sinh (r * A)) ^ 2 :=
    (sq_lt_sq₀ (mul_pos (mul_pos hS hT) (Real.sinh_pos_iff.mpr (mul_pos hr.1 hB))).le
      (mul_pos (mul_pos hC hD) (Real.sinh_pos_iff.mpr (mul_pos hr.1 hA))).le).mpr hprod
  rw [arithmeticDeficit_sum_identity ha hδ]
  change 0 < 4 * ((C * D * Real.sinh (r * A)) ^ 2 - (S * T * Real.sinh (r * B)) ^ 2)
  exact mul_pos (by norm_num) (sub_pos.mpr hsquare)

theorem arithmeticDeficit_sum_zero_identity {δ r : ℝ} (hr : r ∈ Ioo 0 1) :
    arithmeticDeficit δ r 0 + arithmeticDeficit δ (-r) 0 =
      4 * Real.cosh δ ^ 2 * Real.sinh (r * Real.log (Real.cosh δ)) ^ 2 := by
  have hC := Real.cosh_pos δ
  have he₁ : 2 + 2 * r ≠ 0 := by linarith [hr.1]
  have he₂ : 2 + 2 * (-r) ≠ 0 := by linarith [hr.2]
  unfold arithmeticDeficit
  simp only [Real.cosh_zero, Real.sinh_zero, Real.one_rpow, Real.zero_rpow he₁,
    Real.zero_rpow he₂, one_mul, zero_mul, sub_zero, add_zero, zero_add, mul_zero]
  have hp : 2 - 2 * r = 2 + (-2 * r) := by ring
  have hm : 2 - 2 * (-r) = 2 + 2 * r := by ring
  rw [hp, hm, Real.rpow_add hC 2 (-2 * r), Real.rpow_add hC 2 (2 * r), Real.rpow_two]
  have hsym := rpow_symmetric_eq_sinh hC (2 * r)
  rw [show -(2 * r) = -2 * r by ring, show 2 * r * Real.log (Real.cosh δ) / 2 =
    r * Real.log (Real.cosh δ) by ring] at hsym
  rw [Real.cosh_two_mul]
  nlinarith only [hsym, Real.cosh_sq_sub_sinh_sq δ,
    congrArg (fun x : ℝ => Real.cosh δ ^ 2 * x) hsym]

/-- The other strict assertion of equation (15), also at the endpoint. -/
theorem arithmeticDeficit_sum_pos {a δ r : ℝ}
    (ha : 0 ≤ a) (hδ : 0 < δ) (hr : r ∈ Ioo 0 1) :
    0 < arithmeticDeficit δ r a + arithmeticDeficit δ (-r) a := by
  rcases ha.eq_or_lt with ha | ha
  · rw [← ha, arithmeticDeficit_sum_zero_identity hr]
    have hc : 1 < Real.cosh δ := Real.one_lt_cosh.mpr hδ.ne'
    exact mul_pos (mul_pos (by norm_num) (sq_pos_of_ne_zero (Real.cosh_pos _).ne'))
      (sq_pos_of_ne_zero (Real.sinh_pos_iff.mpr (mul_pos hr.1 (Real.log_pos hc))).ne')
  · exact arithmeticDeficit_sum_pos_of_pos ha hδ hr

theorem twoPointNumerator_sub_arithmetic (R p q w : ℝ) :
    twoPointNumerator R p q w -
      2 * Real.cosh R * (w * Real.cosh (2 * p - R) + (1 - w) * Real.cosh (2 * q - R)) =
      arithmeticDeficit (q - p) (-(1 - 2 * w)) p +
        arithmeticDeficit (q - p) (1 - 2 * w) (R - q) := by
  have hpq : p + (q - p) = q := by ring
  have hR : R - q + (q - p) = R - p := by ring
  have he₁ : 2 + 2 * (-(1 - 2 * w)) = 4 * w := by ring
  have he₂ : 2 - 2 * (-(1 - 2 * w)) = 4 * (1 - w) := by ring
  have he₃ : 2 + 2 * (1 - 2 * w) = 4 * (1 - w) := by ring
  have he₄ : 2 - 2 * (1 - 2 * w) = 4 * w := by ring
  unfold arithmeticDeficit twoPointNumerator
  rw [hpq, hR, he₁, he₂, he₃, he₄]
  linear_combination w * (cosh_two_reflected_sum R p) + (1 - w) * (cosh_two_reflected_sum R q)

/-- The complete strict aligned-range inequality of Section 4.3. -/
theorem twoPointRatio_gt_one_aligned {R p q w : ℝ}
    (hp : p ∈ Icc 0 R) (hq : q ∈ Icc 0 R)
    (hpq : p < q) (hw : w ∈ Ioo 0 (1 / 2)) (halign : R ≤ p + q) :
    1 < twoPointRatio R p q w := by
  let δ := q - p
  let r := 1 - 2 * w
  have hδ : 0 < δ := sub_pos.mpr hpq
  have hr : r ∈ Ioo 0 1 := by dsimp [r]; constructor <;> linarith [hw.1, hw.2]
  have ha' : 0 ≤ R - q := sub_nonneg.mpr hq.2
  have hle : R - q ≤ p := by linarith
  have hmono := (strictAntiOn_arithmeticDeficit hδ hr).antitoneOn ha' hp.1 hle
  have hsum := arithmeticDeficit_sum_pos hp.1 hδ hr
  have hstrict : 0 < arithmeticDeficit δ (-r) p + arithmeticDeficit δ r (R - q) := by
    linarith
  have hF : 2 * Real.cosh R *
      (w * Real.cosh (2 * p - R) + (1 - w) * Real.cosh (2 * q - R)) <
        twoPointNumerator R p q w := by
    apply sub_pos.mp
    rw [twoPointNumerator_sub_arithmetic]
    exact hstrict
  have ham := Real.geom_mean_le_arith_mean2_weighted hw.1.le
    (show 0 ≤ 1 - w by linarith [hw.2]) (Real.cosh_pos (2 * p - R)).le
    (Real.cosh_pos (2 * q - R)).le (by ring : w + (1 - w) = 1)
  have hden : twoPointDenominator R p q w ≤ 2 * Real.cosh R *
      (w * Real.cosh (2 * p - R) + (1 - w) * Real.cosh (2 * q - R)) := by
    unfold twoPointDenominator
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left ham
      (mul_pos (by norm_num) (Real.cosh_pos R)).le
  exact (lt_div_iff₀ (twoPointDenominator_pos _ _ _ _)).mpr
    (by simpa only [one_mul] using hden.trans_lt hF)

end PaperVerification.Hyperbolic

#print axioms PaperVerification.Hyperbolic.deriv_arithmeticDeficit_neg
#print axioms PaperVerification.Hyperbolic.strictAntiOn_arithmeticDeficit
#print axioms PaperVerification.Hyperbolic.twoPointRatio_gt_one_aligned

module
public import PaperVerification.HyperbolicBoundary
public import PaperVerification.HyperbolicTwoPoint
public import PaperVerification.HyperbolicDeficits
@[expose] public section
/-! # Boundary derivatives of the literal two-point functional

The derivative identities in this file are obtained directly from equation
(14).  No transformed boundary formula is assumed.
-/

noncomputable section

namespace PaperVerification.Hyperbolic

open Real Set

def twoPointObjective (R p q w : ℝ) : ℝ :=
  Real.log (twoPointNumerator R p q w) - Real.log 2 - Real.log (Real.cosh R) -
    w * Real.log (Real.cosh (2 * p - R)) - (1 - w) * Real.log (Real.cosh (2 * q - R))

def boundaryTermU (q w : ℝ) : ℝ := Real.cosh q ^ (4 * (1 - w))

def boundaryTermV (R q w : ℝ) : ℝ :=
  Real.cosh R ^ (4 * w) * Real.cosh (R - q) ^ (4 * (1 - w))

def boundaryTermW (R q w : ℝ) : ℝ :=
  Real.sinh R ^ (4 * w) * Real.sinh (R - q) ^ (4 * (1 - w))

def boundaryActualX (R q w : ℝ) : ℝ :=
  2 * boundaryTermU q w / twoPointNumerator R 0 q w - 1

def boundaryActualY (R q w : ℝ) : ℝ :=
  2 * boundaryTermW R q w / twoPointNumerator R 0 q w

theorem twoPointDenominator_log (R p q w : ℝ) :
    Real.log (twoPointDenominator R p q w) = Real.log 2 + Real.log (Real.cosh R) +
      w * Real.log (Real.cosh (2 * p - R)) + (1 - w) * Real.log (Real.cosh (2 * q - R)) := by
  unfold twoPointDenominator
  rw [Real.log_mul (mul_ne_zero (mul_ne_zero (by norm_num) (Real.cosh_pos R).ne')
      (Real.rpow_pos_of_pos (Real.cosh_pos _) _).ne')
      (Real.rpow_pos_of_pos (Real.cosh_pos _) _).ne',
    Real.log_mul (mul_ne_zero (by norm_num) (Real.cosh_pos R).ne')
      (Real.rpow_pos_of_pos (Real.cosh_pos _) _).ne',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.cosh_pos R).ne',
    Real.log_rpow (Real.cosh_pos _), Real.log_rpow (Real.cosh_pos _)]

theorem twoPointObjective_eq_log_ratio {R p q w : ℝ}
    (hp : p ∈ Icc 0 R) (hq : q ∈ Icc 0 R) (hw : w ∈ Icc 0 1) :
    twoPointObjective R p q w = Real.log (twoPointRatio R p q w) := by
  rw [twoPointRatio, Real.log_div (twoPointNumerator_pos hp hq hw).ne'
    (twoPointDenominator_pos _ _ _ _).ne', twoPointDenominator_log]
  unfold twoPointObjective
  ring

theorem boundary_numerator (R q w : ℝ) (hw : 0 < w) :
    twoPointNumerator R 0 q w = boundaryTermU q w + boundaryTermV R q w - boundaryTermW R q w := by
  simp only [twoPointNumerator, boundaryTermU, boundaryTermV, boundaryTermW,
    Real.cosh_zero, Real.sinh_zero, Real.one_rpow,
    Real.zero_rpow (mul_pos (by norm_num : (0 : ℝ) < 4) hw).ne',
    one_mul, zero_mul, sub_zero]

theorem hasDerivAt_cosh_rpow (x r : ℝ) :
    HasDerivAt (fun x => Real.cosh x ^ r) (r * Real.tanh x * Real.cosh x ^ r) x := by
  have hc := (Real.cosh_pos x).ne'
  convert (Real.hasDerivAt_cosh x).rpow_const (Or.inl hc) using 1
  · rw [Real.rpow_sub_one hc, Real.tanh_eq_sinh_div_cosh]
    ring

theorem hasDerivAt_sinh_rpow {x : ℝ} (hx : 0 < x) (r : ℝ) :
    HasDerivAt (fun x => Real.sinh x ^ r) (r * coth x * Real.sinh x ^ r) x := by
  have hs := (Real.sinh_pos_iff.mpr hx).ne'
  convert (Real.hasDerivAt_sinh x).rpow_const (Or.inl hs) using 1
  · rw [Real.rpow_sub_one hs]
    unfold coth
    ring

theorem hasDerivAt_sinh_rpow_zero {r : ℝ} (hr : 1 < r) :
    HasDerivAt (fun x => Real.sinh x ^ r) 0 0 := by
  have hd := (Real.hasDerivAt_sinh 0).rpow_const (p := r) (Or.inr hr.le)
  simpa only [Real.sinh_zero, Real.cosh_zero, one_mul,
    Real.zero_rpow (sub_pos.mpr hr).ne', mul_zero] using hd

theorem hasDerivAt_boundaryNumerator_q {R q w : ℝ}
    (hq : q < R) (hw : 0 < w) :
    HasDerivAt (fun q => twoPointNumerator R 0 q w)
      (4 * (1 - w) * (boundaryTermU q w * Real.tanh q -
        boundaryTermV R q w * Real.tanh (R - q) + boundaryTermW R q w * coth (R - q))) q := by
  have hU := hasDerivAt_cosh_rpow q (4 * (1 - w))
  have hV := ((hasDerivAt_cosh_rpow (R - q) (4 * (1 - w))).comp q
    ((hasDerivAt_id q).const_sub R)).const_mul (Real.cosh R ^ (4 * w))
  have hW := ((hasDerivAt_sinh_rpow (sub_pos.mpr hq) (4 * (1 - w))).comp q
    ((hasDerivAt_id q).const_sub R)).const_mul (Real.sinh R ^ (4 * w))
  convert (hU.add hV).sub hW using 1
  · funext q
    exact boundary_numerator R q w hw
  · simp only [boundaryTermU, boundaryTermV, boundaryTermW, Function.comp_apply]
    ring

theorem hasDerivAt_boundaryNumerator_R {R q w : ℝ}
    (hR : 0 < R) (hq : q < R) (hw : 0 < w) :
    HasDerivAt (fun R => twoPointNumerator R 0 q w)
      (boundaryTermV R q w * (4 * w * Real.tanh R + 4 * (1 - w) * Real.tanh (R - q)) -
        boundaryTermW R q w * (4 * w * coth R + 4 * (1 - w) * coth (R - q))) R := by
  have hC := hasDerivAt_cosh_rpow R (4 * w)
  have hD := (hasDerivAt_cosh_rpow (R - q) (4 * (1 - w))).comp R ((hasDerivAt_id R).sub_const q)
  have hS := hasDerivAt_sinh_rpow hR (4 * w)
  have hT := (hasDerivAt_sinh_rpow (sub_pos.mpr hq) (4 * (1 - w))).comp R
    ((hasDerivAt_id R).sub_const q)
  have hd := ((hC.mul hD).const_add (boundaryTermU q w)).sub (hS.mul hT)
  convert hd using 1
  · funext R
    exact boundary_numerator R q w hw
  · simp only [boundaryTermV, boundaryTermW, Function.comp_apply, id_eq]
    ring

theorem hasDerivAt_boundaryNumerator_p {R q w : ℝ}
    (hR : 0 < R) (hw : 1 < 4 * w) :
    HasDerivAt (fun p => twoPointNumerator R p q w)
      (4 * w * (-Real.tanh R * boundaryTermV R q w + coth R * boundaryTermW R q w)) 0 := by
  have hA := (hasDerivAt_cosh_rpow 0 (4 * w)).mul_const (Real.cosh q ^ (4 * (1 - w)))
  have hC := ((hasDerivAt_cosh_rpow (R - 0) (4 * w)).comp 0
    ((hasDerivAt_id 0).const_sub R)).mul_const (Real.cosh (R - q) ^ (4 * (1 - w)))
  have hB := (hasDerivAt_sinh_rpow_zero hw).mul_const (Real.sinh q ^ (4 * (1 - w)))
  have hD := ((hasDerivAt_sinh_rpow (show 0 < R - 0 by simpa only [sub_zero] using hR) (4 * w)).comp 0
    ((hasDerivAt_id 0).const_sub R)).mul_const (Real.sinh (R - q) ^ (4 * (1 - w)))
  simp only [sub_zero] at hC hD
  convert ((hA.add hC).sub hB).sub hD using 1
  · rfl
  · simp only [boundaryTermV, boundaryTermW, Real.tanh_zero, Real.cosh_zero,
      Real.one_rpow, mul_zero, zero_mul, zero_add, add_zero, sub_zero, Function.comp_apply]
    ring

theorem hasDerivAt_boundaryObjective_q {R q w : ℝ}
    (hq : q < R) (hw : 0 < w) (hF : twoPointNumerator R 0 q w ≠ 0) :
    HasDerivAt (fun q => twoPointObjective R 0 q w)
      (4 * (1 - w) * (boundaryTermU q w * Real.tanh q -
        boundaryTermV R q w * Real.tanh (R - q) + boundaryTermW R q w * coth (R - q)) /
          twoPointNumerator R 0 q w - 2 * (1 - w) * Real.tanh (2 * q - R)) q := by
  have hnum := (hasDerivAt_boundaryNumerator_q hq hw).log hF
  have hlast := ((hasDerivAt_log_cosh (2 * q - R)).comp q
    (((hasDerivAt_id q).const_mul 2).sub_const R)).const_mul (1 - w)
  convert (((hnum.sub_const (Real.log 2)).sub_const (Real.log (Real.cosh R))).sub_const
    (w * Real.log (Real.cosh (2 * 0 - R)))).sub hlast using 1
  · rfl
  · ring

theorem hasDerivAt_boundaryObjective_R {R q w : ℝ}
    (hR : 0 < R) (hq : q < R) (hw : 0 < w) (hF : twoPointNumerator R 0 q w ≠ 0) :
    HasDerivAt (fun R => twoPointObjective R 0 q w)
      ((boundaryTermV R q w * (4 * w * Real.tanh R + 4 * (1 - w) * Real.tanh (R - q)) -
        boundaryTermW R q w * (4 * w * coth R + 4 * (1 - w) * coth (R - q))) /
          twoPointNumerator R 0 q w - (1 + w) * Real.tanh R +
            (1 - w) * Real.tanh (2 * q - R)) R := by
  have hnum := (hasDerivAt_boundaryNumerator_R hR hq hw).log hF
  have hmid := ((hasDerivAt_log_cosh (2 * 0 - R)).comp R
    ((hasDerivAt_id R).const_sub (2 * 0))).const_mul w
  have hlast := ((hasDerivAt_log_cosh (2 * q - R)).comp R
    ((hasDerivAt_id R).const_sub (2 * q))).const_mul (1 - w)
  convert (((hnum.sub_const (Real.log 2)).sub (hasDerivAt_log_cosh R)).sub hmid).sub hlast using 1
  · rfl
  · simp only [mul_zero, zero_sub, Real.tanh_neg]
    ring

theorem hasDerivAt_boundaryObjective_p {R q w : ℝ}
    (hR : 0 < R) (hw : 1 < 4 * w) (hF : twoPointNumerator R 0 q w ≠ 0) :
    HasDerivAt (fun p => twoPointObjective R p q w)
      (4 * w * (-Real.tanh R * boundaryTermV R q w + coth R * boundaryTermW R q w) /
        twoPointNumerator R 0 q w + 2 * w * Real.tanh R) 0 := by
  have hnum := (hasDerivAt_boundaryNumerator_p hR hw).log hF
  have hmid := ((hasDerivAt_log_cosh (2 * 0 - R)).comp 0
    (((hasDerivAt_id 0).const_mul 2).sub_const R)).const_mul w
  have hd := (((hnum.sub_const (Real.log 2)).sub_const (Real.log (Real.cosh R))).sub hmid).sub_const
    ((1 - w) * Real.log (Real.cosh (2 * q - R)))
  convert hd using 1
  · rfl
  · simp only [mul_zero, zero_sub, Real.tanh_neg]
    ring

theorem strictMono_tanh : StrictMono Real.tanh := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(hasDerivAt_tanh x).deriv]
  exact sub_pos.mpr (Real.tanh_sq_lt_one x)

theorem tanh_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr hx) (Real.cosh_pos x)

theorem coth_eq_inv_tanh (x : ℝ) : coth x = 1 / Real.tanh x := by
  simp only [coth, Real.tanh_eq_sinh_div_cosh, one_div_div, one_mul]

theorem one_sub_tanh_product_pos (x y : ℝ) : 0 < 1 - Real.tanh x * Real.tanh y := by
  have he : Real.cosh (x - y) = Real.cosh x * Real.cosh y * (1 - Real.tanh x * Real.tanh y) := by
    rw [Real.cosh_sub, Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh]
    field_simp [(Real.cosh_pos x).ne', (Real.cosh_pos y).ne'] <;> ring
  have h := Real.cosh_pos (x - y)
  rw [he] at h
  exact (mul_pos_iff_of_pos_left (mul_pos (Real.cosh_pos x) (Real.cosh_pos y))).mp h

theorem tanh_sub_formula (x y : ℝ) :
    Real.tanh (x - y) = (Real.tanh x - Real.tanh y) / (1 - Real.tanh x * Real.tanh y) := by
  have hn := (one_sub_tanh_product_pos x y).ne'
  apply (eq_div_iff hn).mpr
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_sub, Real.cosh_sub,
    Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh]
  have hc : Real.cosh x * Real.cosh y - Real.sinh x * Real.sinh y ≠ 0 := by
    rw [← Real.cosh_sub]
    exact (Real.cosh_pos _).ne'
  have hc' : -(Real.sinh x * Real.sinh y) + Real.cosh y * Real.cosh x ≠ 0 := by
    convert hc using 1 <;> ring
  field_simp [(Real.cosh_pos x).ne', (Real.cosh_pos y).ne', hc, hc'] <;>
    ring_nf <;> field_simp [hc'] <;> ring

theorem tanh_sub_two_den_pos (x y : ℝ) :
    0 < 1 - 2 * Real.tanh x * Real.tanh y + Real.tanh y ^ 2 := by
  have he : Real.cosh (x - 2 * y) = Real.cosh x * Real.cosh y ^ 2 *
      (1 - 2 * Real.tanh x * Real.tanh y + Real.tanh y ^ 2) := by
    rw [Real.cosh_sub, Real.cosh_two_mul, Real.sinh_two_mul,
      Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh]
    field_simp [(Real.cosh_pos x).ne', (Real.cosh_pos y).ne'] <;> ring
  have h := Real.cosh_pos (x - 2 * y)
  rw [he] at h
  exact (mul_pos_iff_of_pos_left
    (mul_pos (Real.cosh_pos x) (sq_pos_of_ne_zero (Real.cosh_pos y).ne'))).mp h

theorem tanh_sub_two_formula (x y : ℝ) :
    Real.tanh (x - 2 * y) =
      (Real.tanh x - 2 * Real.tanh y + Real.tanh x * Real.tanh y ^ 2) /
        (1 - 2 * Real.tanh x * Real.tanh y + Real.tanh y ^ 2) := by
  apply (eq_div_iff (tanh_sub_two_den_pos x y).ne').mpr
  -- Clear the original cosh denominator before expanding it. Otherwise a
  -- ring normal form can reorder the expanded denominator after field_simp.
  rw [Real.tanh_eq_sinh_div_cosh (x - 2*y), div_mul_eq_mul_div]
  apply (div_eq_iff (Real.cosh_pos (x - 2*y)).ne').mpr
  rw [Real.sinh_sub, Real.cosh_sub, Real.cosh_two_mul, Real.sinh_two_mul]
  simp only [Real.tanh_eq_sinh_div_cosh]
  field_simp [(Real.cosh_pos x).ne', (Real.cosh_pos y).ne'] <;> ring

theorem boundary_tanh_parameters {R q : ℝ} (hq : q ∈ Ioo 0 R) :
    Real.tanh R ^ 2 ∈ Ioo 0 1 ∧ Real.tanh (R - q) / Real.tanh R ∈ Ioo 0 1 := by
  have hR := hq.1.trans hq.2
  have hT := tanh_pos_of_pos hR
  have hV := tanh_pos_of_pos (sub_pos.mpr hq.2)
  have hVT : Real.tanh (R - q) < Real.tanh R := strictMono_tanh (by linarith [hq.1])
  exact ⟨⟨sq_pos_of_ne_zero hT.ne', Real.tanh_sq_lt_one R⟩,
    ⟨div_pos hV hT, (div_lt_one hT).mpr hVT⟩⟩

theorem boundary_tanh_formulas {R q : ℝ} (hq : q ∈ Ioo 0 R) :
    let T := Real.tanh R
    let u := T ^ 2
    let z := Real.tanh (R - q) / T
    Real.tanh q = T * (1 - z) / (1 - u * z) ∧
      Real.tanh (2 * q - R) = T * (1 - 2 * z + u * z ^ 2) / (1 - 2 * u * z + u * z ^ 2) ∧
      Real.tanh (R - q) = T * z := by
  dsimp only
  let T := Real.tanh R
  let u := T ^ 2
  let z := Real.tanh (R - q) / T
  have hT : 0 < T := tanh_pos_of_pos (hq.1.trans hq.2)
  have hV : Real.tanh (R - q) = T * z := by dsimp [z]; field_simp [hT.ne']
  obtain ⟨hu, hz⟩ := boundary_tanh_parameters hq
  change u ∈ Ioo 0 1 at hu
  change z ∈ Ioo 0 1 at hz
  have hb : 0 < 1 - u * z := (boundary_parameters_pos hu hz).2.1
  have hc := (boundary_cd_pos hu hz).1
  refine ⟨?_, ?_, hV⟩
  · change Real.tanh q = T * (1 - z) / (1 - u * z)
    conv_lhs => rw [show q = R - (R - q) by ring]
    rw [tanh_sub_formula, hV]
    change (T - T * z) / (1 - T * (T * z)) = T * (1 - z) / (1 - u * z)
    dsimp [u]
    congr 1 <;> ring
  · change Real.tanh (2 * q - R) =
      T * (1 - 2 * z + u * z ^ 2) / (1 - 2 * u * z + u * z ^ 2)
    rw [show 2 * q - R = R - 2 * (R - q) by ring, tanh_sub_two_formula, hV]
    change (T - 2 * (T * z) + T * (T * z) ^ 2) /
      (1 - 2 * T * (T * z) + (T * z) ^ 2) =
        T * (1 - 2 * z + u * z ^ 2) / (1 - 2 * u * z + u * z ^ 2)
    dsimp [u]
    congr 1 <;> ring

/-- All three actual first derivatives in the variables used by the compact
minimum argument. -/
theorem boundary_actual_derivatives {R q w : ℝ}
    (hq : q ∈ Ioo 0 R) (hw : w ∈ Ioo (1 / 4) (1 / 2)) :
    let T := Real.tanh R
    let u := T ^ 2
    let z := Real.tanh (R - q) / T
    let t := 2 * (1 - w)
    let X := boundaryActualX R q w
    let Y := boundaryActualY R q w
    HasDerivAt (fun q => twoPointObjective R 0 q w)
      (T * boundaryQNormalized u z t X Y) q ∧
    HasDerivAt (fun R => twoPointObjective R 0 q w)
      (T * boundaryRNormalized u z t X Y) R ∧
    HasDerivAt (fun p => twoPointObjective R p q w)
      (2 * w * T * (X + (1 - u) / u * Y)) 0 := by
  dsimp only
  let T := Real.tanh R
  let u := T ^ 2
  let z := Real.tanh (R - q) / T
  let t := 2 * (1 - w)
  let F := twoPointNumerator R 0 q w
  let U := boundaryTermU q w
  let V := boundaryTermV R q w
  let W := boundaryTermW R q w
  have hR := hq.1.trans hq.2
  have hw0 : 0 < w := (by norm_num : (0 : ℝ) < 1 / 4).trans hw.1
  have hw1 : w < 1 := hw.2.trans (by norm_num)
  have hr : 1 < 4 * w := by linarith [hw.1]
  have hF : 0 < F := twoPointNumerator_pos ⟨le_rfl, hR.le⟩ ⟨hq.1.le, hq.2.le⟩ ⟨hw0.le, hw1.le⟩
  have hT : 0 < T := tanh_pos_of_pos hR
  have hFe : F = U + V - W := boundary_numerator R q w hw0
  have hVe : V = F - U + W := by linarith only [hFe]
  obtain ⟨hu, hz⟩ := boundary_tanh_parameters hq
  change u ∈ Ioo 0 1 at hu
  change z ∈ Ioo 0 1 at hz
  have hb := (boundary_parameters_pos hu hz).2.1
  have hc := (boundary_cd_pos hu hz).1
  obtain ⟨hQ, hE, hV⟩ := boundary_tanh_formulas hq
  change Real.tanh q = T * (1 - z) / (1 - u * z) at hQ
  change Real.tanh (2 * q - R) = T * (1 - 2 * z + u * z ^ 2) / (1 - 2 * u * z + u * z ^ 2) at hE
  change Real.tanh (R - q) = T * z at hV
  have hCQ : coth (R - q) = 1 / (T * z) := by rw [coth_eq_inv_tanh, hV]
  have hCR : coth R = 1 / T := coth_eq_inv_tanh R
  have hqb := hasDerivAt_boundaryObjective_q hq.2 hw0 hF.ne'
  have hRb := hasDerivAt_boundaryObjective_R hR hq.2 hw0 hF.ne'
  have hpb := hasDerivAt_boundaryObjective_p hR hr hF.ne'
  refine ⟨?_, ?_, ?_⟩
  · convert hqb using 1
    conv_rhs => rw [hQ, hE, hV, hCQ]
    change T * boundaryQNormalized u z t (2 * U / F - 1) (2 * W / F) =
      4 * (1 - w) * (U * (T * (1 - z) / (1 - u * z)) - V * (T * z) + W * (1 / (T * z))) / F -
        2 * (1 - w) * (T * (1 - 2 * z + u * z ^ 2) / (1 - 2 * u * z + u * z ^ 2))
    rw [hVe]
    unfold boundaryQNormalized
    dsimp [u, t] at *
    field_simp [hF.ne', hT.ne', hz.1.ne', hb.ne', hc.ne'] <;> ring
  · convert hRb using 1
    conv_rhs => rw [hV, hCQ, hCR, hE]
    change T * boundaryRNormalized u z t (2 * U / F - 1) (2 * W / F) =
      (V * (4 * w * T + 4 * (1 - w) * (T * z)) -
        W * (4 * w * (1 / T) + 4 * (1 - w) * (1 / (T * z)))) / F -
          (1 + w) * T + (1 - w) * (T * (1 - 2 * z + u * z ^ 2) / (1 - 2 * u * z + u * z ^ 2))
    rw [hVe]
    unfold boundaryRNormalized
    dsimp [u, t] at *
    field_simp [hF.ne', hT.ne', hz.1.ne', hb.ne', hc.ne'] <;> ring
  · convert hpb using 1
    rw [hCR]
    change 2 * w * T * (2 * U / F - 1 + (1 - u) / u * (2 * W / F)) =
      4 * w * (-T * V + (1 / T) * W) / F + 2 * w * T
    rw [hVe]
    dsimp [u]
    field_simp [hF.ne', hT.ne'] <;> ring

/-- The complete boundary exclusion, retaining the permitted one-sided scale
condition instead of imposing a stationary scale. -/
theorem boundary_inward_deriv_negative {R q w : ℝ}
    (hq : q ∈ Ioo 0 R) (hw : w ∈ Ioo (1 / 4) (1 / 2))
    (hQ : deriv (fun q => twoPointObjective R 0 q w) q = 0)
    (hR : deriv (fun R => twoPointObjective R 0 q w) R ≤ 0) :
    deriv (fun p => twoPointObjective R p q w) 0 < 0 := by
  obtain ⟨hq', hR', hp'⟩ := boundary_actual_derivatives hq hw
  rw [hq'.deriv] at hQ
  rw [hR'.deriv] at hR
  rw [hp'.deriv]
  have hT := tanh_pos_of_pos (hq.1.trans hq.2)
  obtain ⟨hu, hz⟩ := boundary_tanh_parameters hq
  have ht : 1 < 2 * (1 - w) := by linarith [hw.2]
  have hQ' := (mul_eq_zero.mp hQ).resolve_left hT.ne'
  have hR' := nonpos_of_mul_nonpos_right hR hT
  exact mul_neg_of_pos_of_neg
    (mul_pos (mul_pos (by norm_num) ((by norm_num : (0 : ℝ) < 1 / 4).trans hw.1)) hT)
    (boundary_direct_inward_negative hu hz ht hR' hQ')

end PaperVerification.Hyperbolic

#print axioms PaperVerification.Hyperbolic.boundary_actual_derivatives
#print axioms PaperVerification.Hyperbolic.boundary_inward_deriv_negative

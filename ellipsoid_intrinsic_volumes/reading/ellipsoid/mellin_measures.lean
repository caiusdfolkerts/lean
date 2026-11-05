module

public import Ellipsoid.MellinCompactification
public import Ellipsoid.OrderedMomentKernel

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace EllipsoidVerification

def positiveLineLebesgue : Measure PositiveLine :=
  (volume : Measure ℝ).comap Subtype.val

instance positiveLineLebesgue_finiteOnCompacts : IsFiniteMeasureOnCompacts positiveLineLebesgue :=
  IsFiniteMeasureOnCompacts.comap' volume continuous_subtype_val
    (MeasurableEmbedding.subtype_coe measurableSet_Ioi)

instance sigmaFinite_positiveLineLebesgue : SigmaFinite positiveLineLebesgue := by
  apply SigmaFinite.of_map positiveLineLebesgue
    (measurable_subtype_coe : Measurable (Subtype.val : PositiveLine → ℝ)).aemeasurable
  have hmap : positiveLineLebesgue.map (Subtype.val : PositiveLine → ℝ) =
      (volume : Measure ℝ).restrict {t : ℝ | 0 < t} :=
    map_comap_subtype_coe (s := {t : ℝ | 0 < t}) measurableSet_Ioi (volume : Measure ℝ)
  rw [hmap]
  infer_instance

def mellinMeasure {n : ℕ} (e : Coefficients n) (a : ℝ) : Measure PositiveLine :=
  positiveLineLebesgue.withDensity (fun t : PositiveLine => ENNReal.ofReal
    ((t.val : ℝ) ^ (a - 1) * coefficientPolynomial e t.val ^ (-(3 / 2 : ℝ))))

instance sigmaFinite_mellinMeasure {n : ℕ} (e : Coefficients n) (a : ℝ) :
    SigmaFinite (mellinMeasure e a) := by unfold mellinMeasure; infer_instance

@[fun_prop] theorem measurable_mellinDensity {n : ℕ} (e : Coefficients n) (a : ℝ) :
    Measurable (fun t : PositiveLine =>
      (t.val : ℝ) ^ (a - 1) * coefficientPolynomial e t.val ^ (-(3 / 2 : ℝ))) := by
  unfold coefficientPolynomial
  fun_prop

theorem positiveMoment_mellinMeasure {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) (a r : ℝ) :
    positiveMoment (mellinMeasure e a) r = mellinMoment e (a + r) := by
  rw [positiveMoment, mellinMeasure,
    integral_withDensity_eq_integral_toReal_smul (measurable_mellinDensity e a).ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have hfun : (fun t : PositiveLine =>
      (ENNReal.ofReal ((t.val : ℝ) ^ (a - 1) *
        coefficientPolynomial e t.val ^ (-(3 / 2 : ℝ)))).toReal • (t.val : ℝ) ^ r) =
      (fun t : PositiveLine => (t.val : ℝ) ^ (a + r - 1) *
        coefficientPolynomial e t.val ^ (-(3 / 2 : ℝ))) := by
    funext t
    rw [ENNReal.toReal_ofReal (mul_nonneg (Real.rpow_nonneg t.property.le _)
      (Real.rpow_nonneg (coefficientPolynomial_pos he t.val).le _)), smul_eq_mul]
    calc
      t.val ^ (a - 1) * coefficientPolynomial e t.val ^ (-(3 / 2 : ℝ)) * t.val ^ r =
          (t.val ^ (a - 1) * t.val ^ r) * coefficientPolynomial e t.val ^ (-(3 / 2 : ℝ)) := by ring
      _ = _ := by rw [← Real.rpow_add t.property]; congr 2 <;> ring
  rw [hfun]
  exact integral_subtype_comap (s := {t : ℝ | 0 < t}) measurableSet_Ioi
    (fun t : ℝ => t ^ (a + r - 1) * coefficientPolynomial e t ^ (-(3 / 2 : ℝ)))

theorem integrable_mellinMeasure_power {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) {a r : ℝ}
    (har0 : 0 < a + r) (harn : a + r < 3 * n) :
    Integrable (fun t : PositiveLine => (t.val : ℝ) ^ r) (mellinMeasure e a) := by
  rw [mellinMeasure, integrable_withDensity_iff_integrable_smul'
    (measurable_mellinDensity e a).ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have hi : Integrable (fun t : PositiveLine =>
      (t.val : ℝ) ^ (a + r - 1) * coefficientPolynomial e t.val ^ (-(3 / 2 : ℝ)))
      positiveLineLebesgue :=
    (integrableOn_iff_comap_subtypeVal (s := {t : ℝ | 0 < t}) measurableSet_Ioi).1
      (integrable_mellinMoment he har0 harn)
  apply hi.congr
  exact ae_of_all _ fun t => by
    dsimp only
    symm
    rw [ENNReal.toReal_ofReal (mul_nonneg (Real.rpow_nonneg t.property.le _)
      (Real.rpow_nonneg (coefficientPolynomial_pos he t.val).le _)), smul_eq_mul]
    calc
      t.val ^ (a - 1) * coefficientPolynomial e t.val ^ (-(3 / 2 : ℝ)) * t.val ^ r =
          (t.val ^ (a - 1) * t.val ^ r) * coefficientPolynomial e t.val ^ (-(3 / 2 : ℝ)) := by ring
      _ = _ := by rw [← Real.rpow_add t.property]; congr 2 <;> ring

theorem mellinMoment_pos {n : ℕ} {e : Coefficients n} (he : coefficientAdmissible e)
    {r : ℝ} (hr0 : 0 < r) (hrn : r < 3 * n) : 0 < mellinMoment e r := by
  have hpos : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      0 < t ^ (r - 1) * coefficientPolynomial e t ^ (-(3 / 2 : ℝ)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact mul_pos (Real.rpow_pos_of_pos ht _) (Real.rpow_pos_of_pos (coefficientPolynomial_pos he t) _)
  change 0 < ∫ t : ℝ in Ioi 0,
    t ^ (r - 1) * coefficientPolynomial e t ^ (-(3 / 2 : ℝ))
  apply (integral_pos_iff_support_of_nonneg_ae (hpos.mono fun _ hx => hx.le)
    (integrable_mellinMoment he hr0 hrn)).2
  have hs : Function.support (fun t : ℝ => t ^ (r - 1) *
      coefficientPolynomial e t ^ (-(3 / 2 : ℝ))) =ᵐ[volume.restrict (Ioi (0 : ℝ))] univ :=
    hpos.mono fun t ht => by
      apply propext
      constructor
      · intro _
        exact Set.mem_univ t
      · intro _
        exact ht.ne'
  rw [measure_congr hs, Measure.restrict_apply_univ]
  simp

theorem mellinMeasure_ne_zero {n : ℕ} (hn : 0 < n) {e : Coefficients n}
    (he : coefficientAdmissible e) (a : ℝ) : mellinMeasure e a ≠ 0 := by
  intro hzero
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnupper : (n : ℝ) < 3 * n := by linarith
  have hpos := mellinMoment_pos he hnR hnupper
  have hmoment := positiveMoment_mellinMeasure he a ((n : ℝ) - a)
  rw [hzero] at hmoment
  simp only [positiveMoment, integral_zero_measure, add_sub_cancel] at hmoment
  exact hpos.ne' hmoment.symm

def positiveReciprocal : PositiveLine ≃ᵐ PositiveLine where
  toFun t := ⟨t.val⁻¹, inv_pos.mpr t.property⟩
  invFun t := ⟨t.val⁻¹, inv_pos.mpr t.property⟩
  left_inv t := by ext; simp
  right_inv t := by ext; simp
  measurable_toFun := by
    change Measurable (fun t : PositiveLine => (⟨t.val⁻¹, inv_pos.mpr t.property⟩ : PositiveLine))
    exact measurable_subtype_coe.inv.subtype_mk
  measurable_invFun := by
    change Measurable (fun t : PositiveLine => (⟨t.val⁻¹, inv_pos.mpr t.property⟩ : PositiveLine))
    exact measurable_subtype_coe.inv.subtype_mk

@[simp] theorem positiveReciprocal_val (t : PositiveLine) :
    (positiveReciprocal t).val = t.val⁻¹ := rfl

@[simp] theorem positiveReciprocal_involutive (t : PositiveLine) :
    positiveReciprocal (positiveReciprocal t) = t := by
  apply Subtype.ext
  simp only [positiveReciprocal_val, inv_inv]

def reciprocalMellinMeasure {n : ℕ} (e : Coefficients n) (a : ℝ) : Measure PositiveLine :=
  (mellinMeasure e a).map positiveReciprocal

instance sigmaFinite_reciprocalMellinMeasure {n : ℕ} (e : Coefficients n) (a : ℝ) :
    SigmaFinite (reciprocalMellinMeasure e a) := positiveReciprocal.sigmaFinite_map

theorem reciprocalMellinMeasure_ne_zero {n : ℕ} (hn : 0 < n) {e : Coefficients n}
    (he : coefficientAdmissible e) (a : ℝ) : reciprocalMellinMeasure e a ≠ 0 := by
  intro h
  apply mellinMeasure_ne_zero hn he a
  have hmap := congrArg (Measure.map positiveReciprocal) h
  simpa only [reciprocalMellinMeasure, Measure.map_map positiveReciprocal.measurable
    positiveReciprocal.measurable, Function.comp_def,
    show (fun x => positiveReciprocal (positiveReciprocal x)) = id by
      funext t; exact positiveReciprocal_involutive t,
    Measure.map_id, Measure.map_zero] using hmap

theorem positiveMoment_reciprocalMellinMeasure {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) (a r : ℝ) :
    positiveMoment (reciprocalMellinMeasure e a) r = mellinMoment e (a - r) := by
  rw [positiveMoment, reciprocalMellinMeasure, integral_map_equiv positiveReciprocal]
  have hfun : (fun t : PositiveLine => ((positiveReciprocal t).val : ℝ) ^ r) =
      (fun t : PositiveLine => (t.val : ℝ) ^ (-r)) := by
    funext t
    simp only [positiveReciprocal_val, Real.inv_rpow t.property.le, Real.rpow_neg t.property.le]
  rw [hfun]
  exact positiveMoment_mellinMeasure he a (-r)

theorem integrable_reciprocalMellinMeasure_power {n : ℕ} {e : Coefficients n}
    (he : coefficientAdmissible e) {a r : ℝ} (har0 : 0 < a - r) (harn : a - r < 3 * n) :
    Integrable (fun t : PositiveLine => (t.val : ℝ) ^ r) (reciprocalMellinMeasure e a) := by
  rw [reciprocalMellinMeasure, integrable_map_equiv positiveReciprocal]
  have hi := integrable_mellinMeasure_power he (a := a) (r := -r) har0 harn
  convert hi using 1
  funext t
  simp only [Function.comp_apply, positiveReciprocal_val,
    Real.inv_rpow t.property.le, Real.rpow_neg t.property.le]

end EllipsoidVerification

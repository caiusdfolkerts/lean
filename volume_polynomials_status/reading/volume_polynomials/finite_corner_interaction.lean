module

public import VolumePolynomials.FiniteCornerMeasures
public import VolumePolynomials.KernelFourier
public import VolumePolynomials.SlopeEntryEnergy

@[expose] public section
set_option autoImplicit false

/-! # Literal finite cap interactions and their convolution measures

This module identifies the constructed cap's area and slope measure. The
separate mixed-volume identity of Proposition 4.3 is not assumed here.
-/

noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal MeasureTheory ComplexConjugate

namespace VolumePolynomials.HalfZonotope

open PlanarExtrusion

def interactionVector (v w : Plane) : Plane := ((-v.2) * w.1, v.1 * w.2)

def interactionGenerators (vs ws : List Plane) : List Plane :=
  vs.flatMap (fun v => ws.map (interactionVector v))

theorem interactionVector_signed {v w : Plane}
    (hv : 0 ≤ v.1 ∧ v.2 ≤ 0) (hw : 0 ≤ w.1 ∧ w.2 ≤ 0) :
    0 ≤ (interactionVector v w).1 ∧ (interactionVector v w).2 ≤ 0 :=
  ⟨mul_nonneg (neg_nonneg.mpr hv.2) hw.1, mul_nonpos_of_nonneg_of_nonpos hv.1 hw.2⟩

theorem interactionGenerators_signed {vs ws : List Plane}
    (hv : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0)
    (hw : ∀ w ∈ ws, 0 ≤ w.1 ∧ w.2 ≤ 0) :
    ∀ z ∈ interactionGenerators vs ws, 0 ≤ z.1 ∧ z.2 ≤ 0 := by
  first
  | intro z hz
    obtain ⟨v, hv', hz⟩ := List.mem_flatMap.mp hz
    obtain ⟨w, hw', rfl⟩ := List.mem_map.mp hz
    exact interactionVector_signed (hv v hv') (hw w hw')

theorem sum_interactionVector (v : Plane) (ws : List Plane) :
    (ws.map (interactionVector v)).sum = interactionVector v ws.sum := by
  first
  | induction ws with
    | nil => ext <;> simp [interactionVector]
    | cons w ws ih =>
        simp only [List.map_cons, List.sum_cons, ih]
        ext <;> simp [interactionVector, mul_add]

theorem interactionGenerators_sum (vs ws : List Plane) :
    (interactionGenerators vs ws).sum = interactionVector vs.sum ws.sum := by
  first
  | induction vs with
    | nil => ext <;> simp [interactionGenerators, interactionVector]
    | cons v vs ih =>
        simp only [interactionGenerators, List.flatMap_cons, List.sum_append,
          sum_interactionVector, List.sum_cons] at *
        rw [ih]
        ext <;> simp [interactionVector, add_mul] <;> ring

theorem interactionGenerators_unit {vs ws : List Plane}
    (hv : vs.sum = (1, -1)) (hw : ws.sum = (1, -1)) :
    (interactionGenerators vs ws).sum = (1, -1) := by
  first
  | rw [interactionGenerators_sum, hv, hw]
    norm_num [interactionVector]

theorem edgeWeight_interaction {v w : Plane}
    (hv : 0 ≤ v.1 ∧ v.2 ≤ 0) (hw : 0 ≤ w.1 ∧ w.2 ≤ 0) :
    edgeWeight (interactionVector v w) = edgeWeight v * edgeWeight w := by
  first
  | apply NNReal.eq
    change Real.sqrt (((-v.2) * w.1) * (-(v.1 * w.2))) =
      Real.sqrt (v.1 * (-v.2)) * Real.sqrt (w.1 * (-w.2))
    rw [show ((-v.2) * w.1) * (-(v.1 * w.2)) =
      (v.1 * (-v.2)) * (w.1 * (-w.2)) by ring]
    exact Real.sqrt_mul (mul_nonneg hv.1 (neg_nonneg.mpr hv.2)) _

theorem edgeSlope_interaction {v w : Plane}
    (hv : 0 < v.1 ∧ v.2 < 0) (hw : 0 < w.1 ∧ w.2 < 0) :
    edgeSlope (interactionVector v w) = edgeSlope w - edgeSlope v := by
  first
  | have hv2 : 0 < -v.2 := neg_pos.mpr hv.2
    have hw2 : 0 < -w.2 := neg_pos.mpr hw.2
    change Real.log ((-(v.1 * w.2)) / ((-v.2) * w.1)) =
      Real.log ((-w.2) / w.1) - Real.log ((-v.2) / v.1)
    rw [neg_mul_eq_mul_neg, Real.log_div (mul_pos hv.1 hw2).ne'
        (mul_pos hv2 hw.1).ne',
      Real.log_mul hv.1.ne' hw2.ne', Real.log_mul hv2.ne' hw.1.ne',
      Real.log_div hw2.ne' hw.1.ne', Real.log_div hv2.ne' hv.1.ne']
    ring

theorem coordinates_positive_of_edgeWeight_ne_zero {v : Plane}
    (hv : 0 ≤ v.1 ∧ v.2 ≤ 0) (hn : edgeWeight v ≠ 0) :
    0 < v.1 ∧ v.2 < 0 := by
  first
  | constructor
    · by_contra h
      have he : v.1 = 0 := le_antisymm (le_of_not_gt h) hv.1
      apply hn
      apply NNReal.eq
      change Real.sqrt (v.1 * (-v.2)) = 0
      simp [he]
    · by_contra h
      have he : v.2 = 0 := le_antisymm hv.2 (le_of_not_gt h)
      apply hn
      apply NNReal.eq
      change Real.sqrt (v.1 * (-v.2)) = 0
      simp [he]

theorem conv_nnreal_smul (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (a b : ℝ≥0) : (a • μ) ∗ (b • ν) = (a * b) • (μ ∗ ν) := by
  first
  | rw [← Measure.coe_nnreal_smul a, ← Measure.coe_nnreal_smul b,
      Measure.conv_smul_left, Measure.conv_smul_right, smul_smul,
      ← ENNReal.coe_mul, Measure.coe_nnreal_smul]

/-- Each non-axis pair has difference logarithmic slope and product mass;
axis pairs have zero mass on both sides of the same measure identity. -/
theorem edgeMeasure_interaction {v w : Plane}
    (hv : 0 ≤ v.1 ∧ v.2 ≤ 0) (hw : 0 ≤ w.1 ∧ w.2 ≤ 0) :
    edgeMeasure (interactionVector v w) =
      (edgeMeasure v).map Neg.neg ∗ edgeMeasure w := by
  first
  | rw [edgeMeasure, edgeWeight_interaction hv hw]
    unfold edgeMeasure
    rw [Measure.map_smul _ (by fun_prop), Measure.map_dirac' (by fun_prop),
      conv_nnreal_smul, Measure.dirac_conv_dirac]
    by_cases hzv : edgeWeight v = 0
    · simp [hzv]
    by_cases hzw : edgeWeight w = 0
    · simp [hzw]
    rw [edgeSlope_interaction (coordinates_positive_of_edgeWeight_ne_zero hv hzv)
      (coordinates_positive_of_edgeWeight_ne_zero hw hzw)]
    congr 2
    ring

theorem cornerMeasure_append (vs ws : List Plane) :
    cornerMeasure (vs ++ ws) = cornerMeasure vs + cornerMeasure ws := by
  first
  | induction vs with
    | nil => simp [cornerMeasure]
    | cons v vs ih => simp [cornerMeasure, ih, add_assoc, add_comm, add_left_comm]

theorem cornerMeasure_map_interaction {v : Plane} {ws : List Plane}
    (hv : 0 ≤ v.1 ∧ v.2 ≤ 0) (hw : ∀ w ∈ ws, 0 ≤ w.1 ∧ w.2 ≤ 0) :
    cornerMeasure (ws.map (interactionVector v)) =
      (edgeMeasure v).map Neg.neg ∗ cornerMeasure ws := by
  first
  | induction ws with
    | nil => simp [cornerMeasure]
    | cons w ws ih =>
        rw [List.map_cons, cornerMeasure, cornerMeasure,
          ih (fun z hz => hw z (List.mem_cons_of_mem w hz)),
          edgeMeasure_interaction hv (hw w List.mem_cons_self), Measure.conv_add]

/-- The constructed finite cap has exactly the convolution slope measure in
equation (4.11); this does not yet identify its mixed-volume functional. -/
theorem cornerMeasure_interaction {vs ws : List Plane}
    (hv : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0)
    (hw : ∀ w ∈ ws, 0 ≤ w.1 ∧ w.2 ≤ 0) :
    cornerMeasure (interactionGenerators vs ws) =
      (cornerMeasure vs).map Neg.neg ∗ cornerMeasure ws := by
  first
  | induction vs with
    | nil => simp [interactionGenerators, cornerMeasure]
    | cons v vs ih =>
        change cornerMeasure (ws.map (interactionVector v) ++ interactionGenerators vs ws) =
          (cornerMeasure (v :: vs)).map Neg.neg ∗ cornerMeasure ws
        rw [cornerMeasure_append,
          cornerMeasure_map_interaction (hv v List.mem_cons_self) hw,
          ih (fun z hz => hv z (List.mem_cons_of_mem v hz)), cornerMeasure,
          Measure.map_add (cornerMeasure vs) (edgeMeasure v) (by fun_prop),
          Measure.add_conv]
        exact add_comm _ _

theorem charFun_reflect (μ : Measure ℝ) (ξ : ℝ) :
    charFun (μ.map Neg.neg) ξ = conj (charFun μ ξ) := by
  first
  | have h := charFun_map_mul (μ := μ) (-1) ξ
    simpa only [neg_one_mul, charFun_neg] using h

/-- Reflection on one input leaves the self-interaction energy unchanged.
This follows for every finite measure from the proved Fourier identity. -/
theorem reflected_self_convolution_energy (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ‖cornerMean (μ.map Neg.neg ∗ μ)‖ ^ 2 = ‖cornerMean (μ ∗ μ)‖ ^ 2 := by
  first
  | rw [← corner_spectral_energy, ← corner_spectral_energy]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ξ => by
      dsimp only
      rw [charFun_conv, charFun_conv, charFun_reflect]
      simp only [map_mul, Complex.normSq_conj]

theorem area_self_interaction_cap {vs : List Plane}
    (hv : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) (hsum : vs.sum = (1, -1)) :
    volume.real (cap (interactionGenerators vs vs)) =
      1 / 2 - ‖cornerMean (cornerMeasure vs ∗ cornerMeasure vs)‖ ^ 2 / 2 := by
  first
  | rw [area_unit_cap (interactionGenerators_unit hsum hsum),
      cornerEnergy_eq_mean_norm (interactionGenerators_signed hv hv),
      cornerMeasure_interaction hv hv, reflected_self_convolution_energy]

theorem self_convolution_energy_le (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hm : μ.real univ ≤ 1) :
    ‖cornerMean (μ ∗ μ)‖ ^ 2 ≤ ‖cornerMean μ‖ ^ 2 := by
  first
  | rw [← corner_spectral_energy, ← corner_spectral_energy]
    apply integral_mono (integrable_spectral_normSq (μ ∗ μ)) (integrable_spectral_normSq μ)
    intro ξ
    dsimp only
    rw [charFun_conv, map_mul]
    have hn := norm_charFun_le (μ := μ) ξ
    have hn1 : ‖charFun μ ξ‖ ≤ 1 := hn.trans hm
    have he : Complex.normSq (charFun μ ξ) ≤ 1 := by
      first
      | rw [← Complex.sq_norm]
        nlinarith [norm_nonneg (charFun μ ξ)]
    nlinarith [Complex.normSq_nonneg (charFun μ ξ)]

/-- For the literal finite cap family, the interaction area is at least the
input area, including degenerate generators. -/
theorem area_self_interaction_ge {vs : List Plane}
    (hv : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) (hsum : vs.sum = (1, -1)) :
    volume.real (cap vs) ≤ volume.real (cap (interactionGenerators vs vs)) := by
  first
  | have hmoment := unit_cornerMeasure_lintegral_moments hv hsum
    have hm : (cornerMeasure vs).real univ ≤ 1 := by
      first
      | apply slope_mass_le_one
        · simpa [slopeExponentialMoment, div_eq_mul_inv, mul_comm] using hmoment.1
        · simpa [slopeExponentialMoment, div_eq_mul_inv, mul_comm] using hmoment.2
    have henergy := self_convolution_energy_le (cornerMeasure vs) hm
    rw [area_self_interaction_cap hv hsum, area_unit_cap hsum,
      cornerEnergy_eq_mean_norm hv]
    linarith

end VolumePolynomials.HalfZonotope

module

public import VolumePolynomials.FiniteCornerInteraction
public import VolumePolynomials.GeometricCornerInterpolation

@[expose] public section
set_option autoImplicit false

/-! # A continuous range of actual finite caps with a logarithmic interaction gap

All sets and areas in the theorem are literal convex sets and Lebesgue areas.
Identification of the interaction cap with the mixed-volume functional remains
the distinct geometric assertion of Proposition 4.3.
-/

noncomputable section
open Set MeasureTheory
open scoped NNReal MeasureTheory

namespace VolumePolynomials.HalfZonotope

open PlanarExtrusion

theorem edgeWeight_smul (t : ℝ≥0) {v : Plane}
    (hv : 0 ≤ v.1 ∧ v.2 ≤ 0) :
    edgeWeight ((t : ℝ) • v) = t * edgeWeight v := by
  first
  | apply NNReal.eq
    change Real.sqrt ((t * v.1) * (-(t * v.2))) =
      (t : ℝ) * Real.sqrt (v.1 * (-v.2))
    rw [show (t * v.1) * (-(t * v.2)) =
      (t : ℝ) ^ 2 * (v.1 * (-v.2)) by ring,
      Real.sqrt_mul (sq_nonneg (t : ℝ)), Real.sqrt_sq t.coe_nonneg]

theorem edgeMeasure_pos_smul (t : ℝ≥0) (ht : t ≠ 0) {v : Plane}
    (hv : 0 ≤ v.1 ∧ v.2 ≤ 0) :
    edgeMeasure ((t : ℝ) • v) = t • edgeMeasure v := by
  first
  | have htpos : (0 : ℝ) < t := by exact_mod_cast (pos_iff_ne_zero.mpr ht)
    rw [edgeMeasure, edgeWeight_smul t hv, edgeSlope_pos_smul htpos, mul_smul]
    rfl

theorem cornerMeasure_pos_smul (t : ℝ≥0) (ht : t ≠ 0) {vs : List Plane}
    (hv : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) :
    cornerMeasure (vs.map (fun v => (t : ℝ) • v)) = t • cornerMeasure vs := by
  first
  | induction vs with
    | nil => simp [cornerMeasure]
    | cons v vs ih =>
        rw [List.map_cons, cornerMeasure, cornerMeasure,
          ih (fun w hw => hv w (List.mem_cons_of_mem v hw)),
          edgeMeasure_pos_smul t ht (hv v List.mem_cons_self), smul_add]

theorem cornerMeasure_interpolated {t : ℝ} (ht : 0 < t) {vs : List Plane}
    (hv : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) :
    cornerMeasure (interpolatedGenerators t vs) =
      (NNReal.mk t ht.le) • cornerMeasure vs := by
  first
  | have htne : (NNReal.mk t ht.le) ≠ 0 := by
      first
      | intro h
        have he := congrArg (fun r : ℝ≥0 => (r : ℝ)) h
        exact ht.ne' he
    simp only [interpolatedGenerators, cornerMeasure]
    have hhorizontal : edgeMeasure (1 - t, 0) = 0 := by simp [edgeMeasure, edgeWeight]
    have hvertical : edgeMeasure (0, -(1 - t)) = 0 := by simp [edgeMeasure, edgeWeight]
    rw [hhorizontal, hvertical, add_zero, add_zero]
    exact cornerMeasure_pos_smul (NNReal.mk t ht.le) htne hv

theorem cornerMean_nnreal_smul (t : ℝ≥0) (μ : Measure ℝ) :
    cornerMean (t • μ) = (t : ℝ) • cornerMean μ := by
  first
  | simp only [cornerMean, integral_smul_nnreal_measure, NNReal.smul_def]

theorem self_convolution_energy_nnreal_smul (t : ℝ≥0)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ‖cornerMean ((t • μ) ∗ (t • μ))‖ ^ 2 =
      (t : ℝ) ^ 4 * ‖cornerMean (μ ∗ μ)‖ ^ 2 := by
  first
  | rw [conv_nnreal_smul, cornerMean_nnreal_smul, norm_smul]
    simp only [NNReal.coe_mul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg t.coe_nonneg t.coe_nonneg)]
    ring

theorem area_interpolated_self_interaction {n : ℕ} (hn : 0 < n)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    volume.real (cap (interactionGenerators
      (interpolatedGenerators t (geometricGenerators n))
      (interpolatedGenerators t (geometricGenerators n)))) =
        1 / 2 - t ^ 4 * geometricConvolutionDeficit n := by
  first
  | rw [area_self_interaction_cap
        (interpolatedGenerators_signed ⟨ht.1.le, ht.2⟩ (geometricGenerators_signed hn))
        (interpolatedGenerators_sum t (geometricGenerators_sum hn)),
      cornerMeasure_interpolated ht.1 (geometricGenerators_signed hn),
      self_convolution_energy_nnreal_smul]
    dsimp only [geometricConvolutionDeficit, NNReal.coe_mk]
    ring

/-- A full interval of target deficits, with a single positive absolute lower
constant. Both the input and interaction are explicit finite caps. -/
theorem finite_caps_logarithmic_lower_gap {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    ∃ vs : List Plane,
      (∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) ∧ vs.sum = (1, -1) ∧
      volume.real (cap vs) = 1 / 2 - δ ∧
      (3 / 50) * δ ^ 2 * Real.log (1 / δ) ≤
        1 / 2 - volume.real (cap (interactionGenerators vs vs)) := by
  first
  | obtain ⟨n, hn, hδn, hcross⟩ := exists_geometricDeficit_crossing hδ hδhalf
    let t := Real.sqrt (δ / geometricDeficit n)
    have hdn : 0 < geometricDeficit n := lt_of_lt_of_le hδ hδn
    have htpos : 0 < t := Real.sqrt_pos.mpr (div_pos hδ hdn)
    obtain ⟨ht, hscale⟩ := geometric_interpolation_parameter hδ hn hδn
    refine ⟨interpolatedGenerators t (geometricGenerators n),
      interpolatedGenerators_signed ht (geometricGenerators_signed hn),
      interpolatedGenerators_sum t (geometricGenerators_sum hn), ?_, ?_⟩
    · rw [area_interpolated_cap ht (geometricGenerators_signed hn) (geometricGenerators_sum hn),
        area_geometricCap hn]
      nlinarith
    · rw [area_interpolated_self_interaction hn ⟨htpos, ht.2⟩]
      have hη := mul_le_mul_of_nonneg_left (geometricConvolutionDeficit_lower hn)
        (by positivity : 0 ≤ t ^ 4)
      have hsquare : t ^ 4 * geometricDeficit n ^ 2 = δ ^ 2 := by
        first
        | have hs := congrArg (fun x : ℝ => x ^ 2) hscale
          dsimp only [t] at *
          nlinarith
      have hlog := mul_le_mul_of_nonneg_left (logarithm_le_crossing_index hδ hn hcross)
        (sq_nonneg δ)
      nlinarith

end VolumePolynomials.HalfZonotope

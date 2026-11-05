module

public import VolumePolynomials.FiniteCornerCaps
public import VolumePolynomials.SlopeAtomKernel

@[expose] public section
set_option autoImplicit false

/-! # Actual slope measures and the exact area of finite convex caps -/

noncomputable section
open MeasureTheory Set
open scoped NNReal InnerProductSpace RealInnerProductSpace

namespace VolumePolynomials.HalfZonotope

open PlanarExtrusion

def edgeSlope (v : Plane) : ℝ := Real.log ((-v.2) / v.1)

def edgeWeight (v : Plane) : ℝ≥0 :=
  NNReal.mk (Real.sqrt (v.1 * (-v.2))) (Real.sqrt_nonneg _)

def edgeVector (v : Plane) : Lp ℝ 2 (volume : Measure ℝ) :=
  (edgeWeight v : ℝ) • cornerFeature (edgeSlope v)

def edgeMeasure (v : Plane) : Measure ℝ :=
  edgeWeight v • Measure.dirac (edgeSlope v)

instance edgeMeasure_finite (v : Plane) : IsFiniteMeasure (edgeMeasure v) := by
  first
  | unfold edgeMeasure
    infer_instance

def cornerMeasure : List Plane → Measure ℝ
  | [] => 0
  | v :: vs => cornerMeasure vs + edgeMeasure v

instance cornerMeasure_finite (vs : List Plane) : IsFiniteMeasure (cornerMeasure vs) := by
  first
  | induction vs with
    | nil => dsimp only [cornerMeasure]; infer_instance
    | cons v vs ih =>
        letI : IsFiniteMeasure (cornerMeasure vs) := ih
        change IsFiniteMeasure (cornerMeasure vs + edgeMeasure v)
        infer_instance

theorem integrable_edgeMeasure (v : Plane) (f : ℝ → ℝ) : Integrable f (edgeMeasure v) :=
  (integrable_dirac (f := f) (a := edgeSlope v) enorm_lt_top).smul_measure_nnreal

theorem integrable_cornerMeasure (vs : List Plane) (f : ℝ → ℝ) :
    Integrable f (cornerMeasure vs) := by
  first
  | induction vs with
    | nil => exact integrable_zero_measure
    | cons v vs ih => exact ih.add_measure (integrable_edgeMeasure v f)

theorem integral_edgeMeasure (v : Plane) (f : ℝ → ℝ) :
    (∫ x, f x ∂edgeMeasure v) = (edgeWeight v : ℝ) * f (edgeSlope v) := by
  first
  | change (∫ x, f x ∂(edgeWeight v • Measure.dirac (edgeSlope v))) = _
    rw [integral_smul_nnreal_measure, integral_dirac]
    rfl

theorem edgeMeasure_exponential_moments_le {v : Plane}
    (hv : 0 ≤ v.1 ∧ v.2 ≤ 0) :
    (∫ x, Real.exp (-x / 2) ∂edgeMeasure v) ≤ v.1 ∧
      (∫ x, Real.exp (x / 2) ∂edgeMeasure v) ≤ -v.2 := by
  first
  | rw [integral_edgeMeasure, integral_edgeMeasure]
    change Real.sqrt (v.1 * (-v.2)) * Real.exp (-Real.log ((-v.2) / v.1) / 2) ≤ v.1 ∧
      Real.sqrt (v.1 * (-v.2)) * Real.exp (Real.log ((-v.2) / v.1) / 2) ≤ -v.2
    by_cases ha : v.1 = 0
    · simpa [ha] using neg_nonneg.mpr hv.2
    by_cases hb : v.2 = 0
    · simpa [hb] using hv.1
    have hm := atom_exponential_moments (lt_of_le_of_ne hv.1 (Ne.symm ha))
      (neg_pos.mpr (lt_of_le_of_ne hv.2 hb))
    exact ⟨hm.1.le, hm.2.le⟩

/-- Omitting axis edges can only decrease the signed coordinate totals. -/
theorem cornerMeasure_exponential_moments_le {vs : List Plane}
    (hvs : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) :
    (∫ x, Real.exp (-x / 2) ∂cornerMeasure vs) ≤ vs.sum.1 ∧
      (∫ x, Real.exp (x / 2) ∂cornerMeasure vs) ≤ -vs.sum.2 := by
  first
  | induction vs with
    | nil => simp [cornerMeasure]
    | cons v vs ih =>
        have hv := edgeMeasure_exponential_moments_le (hvs v List.mem_cons_self)
        have ht := ih (fun w hw => hvs w (List.mem_cons_of_mem v hw))
        simp only [cornerMeasure, integral_add_measure (integrable_cornerMeasure vs _)
          (integrable_edgeMeasure v _), List.sum_cons, Prod.fst_add, Prod.snd_add]
        constructor <;> linarith

/-- The genuine nonnegative integrals, so nonintegrability cannot make the
moment condition vacuous. -/
theorem unit_cornerMeasure_lintegral_moments {vs : List Plane}
    (hvs : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) (hsum : vs.sum = (1, -1)) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (-x / 2)) ∂cornerMeasure vs) ≤ 1 ∧
      (∫⁻ x, ENNReal.ofReal (Real.exp (x / 2)) ∂cornerMeasure vs) ≤ 1 := by
  first
  | have h := cornerMeasure_exponential_moments_le hvs
    rw [hsum] at h
    constructor
    · rw [← ofReal_integral_eq_lintegral_ofReal (integrable_cornerMeasure vs _)
        (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)]
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal h.1
    · rw [← ofReal_integral_eq_lintegral_ofReal (integrable_cornerMeasure vs _)
        (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)]
      simpa using ENNReal.ofReal_le_ofReal h.2

theorem inner_edgeVector {v w : Plane}
    (hv : 0 ≤ v.1 ∧ v.2 ≤ 0) (hw : 0 ≤ w.1 ∧ w.2 ≤ 0) :
    ⟪edgeVector v, edgeVector w⟫_ℝ = cornerInteraction v w := by
  first
  | have h := weighted_cornerKernel hv.1 (neg_nonneg.mpr hv.2)
      hw.1 (neg_nonneg.mpr hw.2)
    simpa only [edgeVector, real_inner_smul_left, real_inner_smul_right, inner_cornerFeature,
      edgeWeight, edgeSlope, NNReal.coe_mk, cornerInteraction,
      mul_comm, mul_left_comm, mul_assoc] using h

theorem cornerMean_edgeMeasure (v : Plane) : cornerMean (edgeMeasure v) = edgeVector v := by
  first
  | simp only [cornerMean, edgeMeasure, integral_smul_nnreal_measure, integral_dirac,
      NNReal.smul_def, edgeVector]

theorem cornerMean_cons (v : Plane) (vs : List Plane) :
    cornerMean (cornerMeasure (v :: vs)) = cornerMean (cornerMeasure vs) + edgeVector v := by
  first
  | change (∫ x, cornerFeature x ∂(cornerMeasure vs + edgeMeasure v)) = _
    rw [integral_add_measure (integrable_cornerFeature _) (integrable_cornerFeature _)]
    exact congrArg (cornerMean (cornerMeasure vs) + ·) (cornerMean_edgeMeasure v)

theorem inner_cornerMean_edgeVector {vs : List Plane} {v : Plane}
    (hvs : ∀ w ∈ vs, 0 ≤ w.1 ∧ w.2 ≤ 0) (hv : 0 ≤ v.1 ∧ v.2 ≤ 0) :
    ⟪cornerMean (cornerMeasure vs), edgeVector v⟫_ℝ =
      (vs.map (cornerInteraction v)).sum := by
  first
  | induction vs with
    | nil => simp [cornerMeasure, cornerMean]
    | cons w vs ih =>
        rw [cornerMean_cons, inner_add_left, ih (fun z hz => hvs z (List.mem_cons_of_mem w hz)),
          real_inner_comm (edgeVector v) (edgeVector w),
          inner_edgeVector hv (hvs w List.mem_cons_self)]
        simp only [List.map_cons, List.sum_cons, add_comm]

/-- The finite algebraic energy equals the genuine double exponential-kernel
integral of the actual slope measure. Axis generators automatically carry zero mass. -/
theorem cornerEnergy_eq_mean_norm {vs : List Plane}
    (hvs : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) :
    cornerEnergy vs = ‖cornerMean (cornerMeasure vs)‖ ^ 2 := by
  first
  | induction vs with
    | nil => simp [cornerEnergy, cornerMeasure, cornerMean]
    | cons v vs ih =>
        have hv := hvs v List.mem_cons_self
        have ht := fun w hw => hvs w (List.mem_cons_of_mem v hw)
        rw [cornerMean_cons, norm_add_sq_real,
          inner_cornerMean_edgeVector ht hv, ← ih ht]
        have hn : ‖edgeVector v‖ ^ 2 = v.1 * (-v.2) := by
          first
          | rw [← real_inner_self_eq_norm_sq, inner_edgeVector hv hv]
            simp [cornerInteraction]
        rw [hn]
        dsimp only [cornerEnergy]
        ring

theorem area_cap_eq_kernel_energy {vs : List Plane}
    (hvs : ∀ v ∈ vs, 0 ≤ v.1 ∧ v.2 ≤ 0) (hsum : vs.sum = (1, -1)) :
    volume.real (cap vs) = 1 / 2 -
      (1 / 2) * (∫ x, ∫ y, cornerKernel x y ∂cornerMeasure vs ∂cornerMeasure vs) := by
  first
  | rw [area_unit_cap hsum, cornerEnergy_eq_mean_norm hvs, norm_cornerMean_sq]
    ring

end VolumePolynomials.HalfZonotope

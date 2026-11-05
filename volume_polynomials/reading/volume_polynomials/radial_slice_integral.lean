module

public import VolumePolynomials.ClippedConeVolume
public import VolumePolynomials.ConeDerivative

@[expose] public section
set_option autoImplicit false

/-! # Finite radial slice integrals

Actual nonnegative cone fibers are converted to finite real integrals. Uniform
bounds come from a containing radial interval, while exact interval fibers
give the elementary power primitive used in first variation.
-/

noncomputable section
open Set MeasureTheory Module
open scoped ENNReal Topology

namespace VolumePolynomials.ClippedConeVolume

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def radialSlice (k : ℕ) (R : ℝ) (K : Set (ℝ × E)) (x : E) : ℝ :=
  (∫⁻ r in Icc (0 : ℝ) R, radialWeight k K (r, x)).toReal

theorem lintegral_radial_pow (k : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    (∫⁻ r in Icc (0 : ℝ) R, ENNReal.ofReal (r ^ k)) =
      ENNReal.ofReal (R ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) := by
  first
  | have hi : IntegrableOn (fun r : ℝ => r ^ k) (Icc (0 : ℝ) R) :=
      (continuous_id.pow k).integrableOn_Icc
    have hn : 0 ≤ᵐ[volume.restrict (Icc (0 : ℝ) R)] (fun r : ℝ => r ^ k) := by
      first
      | filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
        exact pow_nonneg hr.1 _
    rw [← ofReal_integral_eq_lintegral_ofReal hi hn,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hR, integral_pow]
    simp

theorem lintegral_radialWeight_le (k : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (K : Set (ℝ × E)) (x : E) :
    (∫⁻ r in Icc (0 : ℝ) R, radialWeight k K (r, x)) ≤
      ENNReal.ofReal (R ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) := by
  first
  | rw [← lintegral_radial_pow k hR]
    apply lintegral_mono
    intro r
    by_cases h : radialMap (r, x) ∈ K
    · simp [radialWeight, h]
    · simp [radialWeight, h]

theorem lintegral_radialWeight_lt_top (k : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (K : Set (ℝ × E)) (x : E) :
    (∫⁻ r in Icc (0 : ℝ) R, radialWeight k K (r, x)) < ∞ :=
  (lintegral_radialWeight_le k hR K x).trans_lt ENNReal.ofReal_lt_top

theorem radialSlice_nonneg (k : ℕ) (R : ℝ) (K : Set (ℝ × E)) (x : E) :
    0 ≤ radialSlice k R K x := ENNReal.toReal_nonneg

theorem radialSlice_le (k : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (K : Set (ℝ × E)) (x : E) :
    radialSlice k R K x ≤ R ^ (k + 1) / ((k + 1 : ℕ) : ℝ) := by
  first
  | have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (lintegral_radialWeight_le k hR K x)
    simpa only [radialSlice, ENNReal.toReal_ofReal
      (div_nonneg (pow_nonneg hR _) (Nat.cast_nonneg _))] using h

theorem radialSlice_mono (k : ℕ) {R : ℝ} (hR : 0 ≤ R)
    {K L : Set (ℝ × E)} (hKL : K ⊆ L) (x : E) :
    radialSlice k R K x ≤ radialSlice k R L x := by
  first
  | apply ENNReal.toReal_mono (lintegral_radialWeight_lt_top k hR L x).ne
    apply lintegral_mono
    intro r
    by_cases h : radialMap (r, x) ∈ K
    · simp [radialWeight, h, hKL h]
    · simp [radialWeight, h]

theorem radialSlice_mono_on_ray (k : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (K L : Set (ℝ × E)) (x : E)
    (hKL : ∀ r : ℝ, 0 ≤ r → radialMap (r, x) ∈ K → radialMap (r, x) ∈ L) :
    radialSlice k R K x ≤ radialSlice k R L x := by
  first
  | apply ENNReal.toReal_mono (lintegral_radialWeight_lt_top k hR L x).ne
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    by_cases h : radialMap (r, x) ∈ K
    · simp [radialWeight, h, hKL r hr.1 h]
    · simp [radialWeight, h]

theorem radialSlice_eq_power_of_interval (k : ℕ) {R L : ℝ}
    (hL : 0 ≤ L) (hLR : L ≤ R) (K : Set (ℝ × E)) (x : E)
    (hfiber : ∀ r : ℝ, 0 ≤ r → (radialMap (r, x) ∈ K ↔ r ≤ L)) :
    radialSlice k R K x = L ^ (k + 1) / ((k + 1 : ℕ) : ℝ) := by
  first
  | have heq : (∫⁻ r in Icc (0 : ℝ) R, radialWeight k K (r, x)) =
        ∫⁻ r in Icc (0 : ℝ) R,
          (Icc (0 : ℝ) L).indicator (fun s => ENNReal.ofReal (s ^ k)) r := by
      first
      | apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
        by_cases hrL : r ≤ L
        · have hrI : r ∈ Icc (0 : ℝ) L := ⟨hr.1, hrL⟩
          simp [radialWeight, (hfiber r hr.1).mpr hrL, Set.indicator_of_mem hrI]
        · simp [radialWeight, (hfiber r hr.1).not.mpr hrL, Set.indicator_of_notMem
            (show r ∉ Icc (0 : ℝ) L from fun h => hrL h.2)]
    have hsub : Icc (0 : ℝ) L ⊆ Icc (0 : ℝ) R := fun r hr => ⟨hr.1, hr.2.trans hLR⟩
    rw [radialSlice, heq, setLIntegral_indicator measurableSet_Icc,
      inter_eq_left.mpr hsub, lintegral_radial_pow k hL,
      ENNReal.toReal_ofReal (div_nonneg (pow_nonneg hL _) (Nat.cast_nonneg _))]

theorem radialSlice_le_power_of_upper_bound (k : ℕ) {R L : ℝ}
    (hL : 0 ≤ L) (hLR : L ≤ R) (K : Set (ℝ × E)) (x : E)
    (hupper : ∀ r : ℝ, 0 ≤ r → radialMap (r, x) ∈ K → r ≤ L) :
    radialSlice k R K x ≤ L ^ (k + 1) / ((k + 1 : ℕ) : ℝ) := by
  first
  | let S : Set (ℝ × E) := {p | p.1 ≤ L}
    have hm := radialSlice_mono_on_ray k (hL.trans hLR) K S x hupper
    rw [radialSlice_eq_power_of_interval k hL hLR S x (fun _ _ => Iff.rfl)] at hm
    exact hm

theorem power_le_radialSlice_of_lower_bound (k : ℕ) {R L : ℝ}
    (hL : 0 ≤ L) (hLR : L ≤ R) (K : Set (ℝ × E)) (x : E)
    (hlower : ∀ r : ℝ, 0 ≤ r → r ≤ L → radialMap (r, x) ∈ K) :
    L ^ (k + 1) / ((k + 1 : ℕ) : ℝ) ≤ radialSlice k R K x := by
  first
  | let S : Set (ℝ × E) := {p | p.1 ≤ L}
    have hm := radialSlice_mono_on_ray k (hL.trans hLR) S K x hlower
    rw [radialSlice_eq_power_of_interval k hL hLR S x (fun _ _ => Iff.rfl)] at hm
    exact hm

section Measurable

variable [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

theorem measurable_radialSlice (k : ℕ) (R : ℝ) {K : Set (ℝ × E)}
    (hK : MeasurableSet K) : Measurable (radialSlice k R K) :=
  ((measurable_radialWeight k hK).lintegral_prod_left'
    (μ := volume.restrict (Icc (0 : ℝ) R))).ennreal_toReal

theorem integrableOn_radialSlice (k : ℕ) {R : ℝ} (hR : 0 ≤ R)
    {A : Set E} (hA : IsCompact A) {K : Set (ℝ × E)} (hK : MeasurableSet K) :
    IntegrableOn (radialSlice k R K) A := by
  first
  | letI : IsFiniteMeasure (volume.restrict A) := ⟨by
      simpa only [Measure.restrict_apply_univ] using hA.measure_lt_top⟩
    apply (integrable_const (R ^ (k + 1) / ((k + 1 : ℕ) : ℝ))).mono'
      (measurable_radialSlice k R hK).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (radialSlice_nonneg k R K x)]
      exact radialSlice_le k hR K x

theorem realVolume_clippedCone {R : ℝ} (hR : 0 ≤ R) {A : Set E} (hA : IsCompact A)
    {K : Set (ℝ × E)} (hK : IsClosed K) :
    volume.real (clippedCone R A K) = ∫ x in A, radialSlice (finrank ℝ E) R K x := by
  first
  | rw [measureReal_def, volume_clippedCone hA hK]
    exact (integral_toReal
      ((measurable_radialWeight (finrank ℝ E) hK.measurableSet).lintegral_prod_left'
        (μ := volume.restrict (Icc (0 : ℝ) R))).aemeasurable
      (Filter.Eventually.of_forall fun x => lintegral_radialWeight_lt_top _ hR K x)).symm

end Measurable
end VolumePolynomials.ClippedConeVolume

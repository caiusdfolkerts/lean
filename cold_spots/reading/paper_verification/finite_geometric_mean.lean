module
public import PaperVerification.GeometricMeanLaws
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Measure.Count
@[expose] public section
noncomputable section

namespace PaperVerification.Hyperbolic

open MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal

variable (X : Type*) [Fintype X] [Nonempty X] [MeasurableSpace X]
  [MeasurableSingletonClass X]

/-- The genuine uniform probability measure on an arbitrary nonempty finite type. -/
def uniformProbability : ProbabilityMeasure X := by
  refine ⟨(Fintype.card X : ℝ≥0∞)⁻¹ • (Measure.count : Measure X), ⟨?_⟩⟩
  have hc : (Measure.count : Measure X) univ = (Fintype.card X : ℝ≥0∞) := by
    simpa only [Finset.coe_univ, Finset.card_univ] using
      (Measure.count_apply_finset (Finset.univ : Finset X))
  rw [Measure.smul_apply, smul_eq_mul, hc]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero)
    (ENNReal.natCast_ne_top _)

theorem ae_uniformProbability_iff (p : X → Prop) :
    (∀ᵐ x ∂(uniformProbability X : Measure X), p x) ↔ ∀ x, p x := by
  change (∀ᵐ x ∂(Fintype.card X : ℝ≥0∞)⁻¹ • (Measure.count : Measure X), p x) ↔ _
  rw [Measure.ae_ennreal_smul_measure_iff (by simp : (Fintype.card X : ℝ≥0∞)⁻¹ ≠ 0),
    Measure.ae_count_iff]

theorem integral_uniformProbability (f : X → ℝ) :
    (∫ x, f x ∂(uniformProbability X : Measure X)) =
      (∑ x, f x) / (Fintype.card X : ℝ) := by
  change (∫ x, f x ∂(Fintype.card X : ℝ≥0∞)⁻¹ • (Measure.count : Measure X)) = _
  rw [integral_smul_measure, integral_count]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul, div_eq_mul_inv, mul_comm]

variable [TopologicalSpace X] [CompactSpace X] [OpensMeasurableSpace X]

/-- Finite-product formula, proved with every zero-factor case included. -/
theorem geometricMoment_uniformProbability (k : ℝ) (hk : 0 < k) (f : C(X, ℝ))
    (hf : ∀ x, 0 ≤ f x) :
    geometricMoment k f (uniformProbability X) =
      (∏ x, f x) ^ (k / (Fintype.card X : ℝ)) := by
  have hn : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  by_cases hpos : ∀ x, 0 < f x
  · let logf : C(X, ℝ) := ⟨fun x ↦ Real.log (f x),
      f.continuous.log (fun x ↦ (hpos x).ne')⟩
    rw [geometricMoment_eq_exp_integral_of_integrable_log k hk.le f
      (uniformProbability X) (Eventually.of_forall hpos)
      (integrable_continuousMap logf (uniformProbability X)), integral_uniformProbability,
      Real.rpow_def_of_pos (Finset.prod_pos (fun x _ ↦ hpos x)),
      Real.log_prod (fun x _ ↦ (hpos x).ne')]
    congr 1
    ring
  · obtain ⟨x, hx⟩ := not_forall.mp hpos
    have hxzero : f x = 0 := le_antisymm (le_of_not_gt hx) (hf x)
    have hz : geometricMoment k f (uniformProbability X) = 0 := by
      apply (geometricMoment_eq_zero_iff k hk f (uniformProbability X) hf).mpr
      rintro ⟨hae, _⟩
      have hall := (ae_uniformProbability_iff X (fun x ↦ 0 < f x)).mp hae
      exact hx (hall x)
    have hprod : (∏ x, f x) = 0 := Finset.prod_eq_zero (Finset.mem_univ x) hxzero
    rw [hz, hprod, Real.zero_rpow (div_pos hk hn).ne']

theorem geometricMean_uniformProbability (f : C(X, ℝ)) (hf : ∀ x, 0 ≤ f x) :
    geometricMean f (uniformProbability X) =
      (∏ x, f x) ^ (1 / (Fintype.card X : ℝ)) :=
  geometricMoment_uniformProbability X 1 zero_lt_one f hf

end PaperVerification.Hyperbolic

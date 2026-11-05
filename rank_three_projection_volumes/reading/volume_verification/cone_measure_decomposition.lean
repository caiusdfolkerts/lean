module
public import VolumeVerification.ConeSelection
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
@[expose] public section
set_option autoImplicit false

/-!
# Decomposing a positive vector of measures along a finite cone

The Radon--Nikodym densities and the measurable cone selector give finite
positive measures on the generators.  All signed relations are expressed as
equalities of the actual real masses on measurable sets.
-/
namespace VolumeVerification.ConeMeasureDecomposition
open scoped BigOperators ENNReal Matrix
open MeasureTheory Set

variable {Ω ι κ ζ : Type*} [MeasurableSpace Ω]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype ζ] [DecidableEq ζ]

theorem withDensity_finsetSum (μ : Measure Ω) (s : Finset κ)
    (f : κ → Ω → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    μ.withDensity (fun x => ∑ i ∈ s, f i x) =
      ∑ i ∈ s, μ.withDensity (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [withDensity_zero]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      change μ.withDensity (f i + fun x => ∑ j ∈ s, f j x) =
        μ.withDensity (f i) + ∑ j ∈ s, μ.withDensity (f j)
      rw [withDensity_add_left (hf i), ih]

theorem decompose_density (μ : Measure Ω)
    (r : κ → ι → ℝ) (hr : ∀ e i, 0 ≤ r e i)
    (a : Ω → ι → ℝ) (ha : Measurable a) (hai : Integrable a μ)
    (hcone : ∀ᵐ x ∂μ, ∃ c : κ → ℝ,
      (∀ e, 0 ≤ c e) ∧ ∑ e, c e • r e = a x) :
    ∃ ν : κ → Measure Ω,
      (∀ e, IsFiniteMeasure (ν e)) ∧
      ∀ i, μ.withDensity (fun x => ENNReal.ofReal (a x i)) =
        ∑ e, ENNReal.ofReal (r e i) • ν e := by
  classical
  obtain ⟨hselect,hselectpos,hreconstruct,C,hC,hbound⟩ :=
    ConeSelection.measurable_cone_coefficients r
  let c : Ω → κ → ℝ := fun x => ConeSelection.select r (a x)
  have hc : Measurable c := hselect.comp ha
  have hcpos : ∀ x e, 0 ≤ c x e := fun x e => hselectpos (a x) e
  have hci : Integrable c μ :=
    (hai.norm.const_mul C).mono' hc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => hbound (a x))
  let ν : κ → Measure Ω :=
    fun e => μ.withDensity (fun x => ENNReal.ofReal (c x e))
  have hνfinite : ∀ e, IsFiniteMeasure (ν e) := by
    intro e
    apply isFiniteMeasure_withDensity
    exact (lintegral_ofReal_ne_top_iff_integrable
      (hci.eval e).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => hcpos x e)).mpr (hci.eval e)
  refine ⟨ν,hνfinite,?_⟩
  intro i
  have heq : (fun x => ENNReal.ofReal (a x i)) =ᵐ[μ]
      (fun x => ∑ e, ENNReal.ofReal (r e i) * ENNReal.ofReal (c x e)) := by
    filter_upwards [hcone] with x hx
    have hx' := congrFun (hreconstruct (a x) hx) i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hx'
    rw [← hx', ENNReal.ofReal_sum_of_nonneg
      (fun e _ => mul_nonneg (hcpos x e) (hr e i))]
    apply Finset.sum_congr rfl
    intro e _
    rw [ENNReal.ofReal_mul (hcpos x e)]
    exact mul_comm _ _
  rw [withDensity_congr_ae heq,
    withDensity_finsetSum μ Finset.univ
      (fun e x => ENNReal.ofReal (r e i) * ENNReal.ofReal (c x e))
      (fun e => measurable_const.mul ((measurable_pi_apply e).comp hc).ennreal_ofReal)]
  apply Finset.sum_congr rfl
  intro e _
  change μ.withDensity (ENNReal.ofReal (r e i) •
      (fun x => ENNReal.ofReal (c x e))) =
    ENNReal.ofReal (r e i) • μ.withDensity (fun x => ENNReal.ofReal (c x e))
  exact withDensity_smul _ (((measurable_pi_apply e).comp hc).ennreal_ofReal)

noncomputable def realDensity (μ : Measure Ω) (μi : ι → Measure Ω) :
    Ω → ι → ℝ :=
  fun x i => ((μi i).rnDeriv μ x).toReal

theorem realDensity_measurable (μ : Measure Ω) (μi : ι → Measure Ω) :
    Measurable (realDensity μ μi) :=
  Measurable.of_eval fun i => ((μi i).measurable_rnDeriv μ).ennreal_toReal

theorem realDensity_integrable (μ : Measure Ω) (μi : ι → Measure Ω)
    [∀ i, IsFiniteMeasure (μi i)] :
    Integrable (realDensity μ μi) μ := by
  apply integrable_pi_iff.mpr
  intro i
  simpa only [integrableOn_univ, realDensity] using
    (Measure.integrableOn_toReal_rnDeriv (μ := μi i) (ν := μ)
      (s := Set.univ) (measure_ne_top (μi i) Set.univ))

theorem realDensity_reconstructs (μ : Measure Ω) (μi : ι → Measure Ω)
    [IsFiniteMeasure μ] [∀ i, IsFiniteMeasure (μi i)]
    (hdom : ∀ i, μi i ≤ μ) (i : ι) :
    μ.withDensity (fun x => ENNReal.ofReal (realDensity μ μi x i)) = μi i := by
  have heq : (fun x => ENNReal.ofReal (realDensity μ μi x i)) =ᵐ[μ]
      (μi i).rnDeriv μ := by
    filter_upwards [Measure.rnDeriv_ne_top (μi i) μ] with x hx
    exact ENNReal.ofReal_toReal hx
  rw [withDensity_congr_ae heq]
  exact Measure.withDensity_rnDeriv_eq _ _ (hdom i).absolutelyContinuous

theorem realDensity_linear_relations (μ : Measure Ω) (μi : ι → Measure Ω)
    [IsFiniteMeasure μ] [∀ i, IsFiniteMeasure (μi i)]
    (hdom : ∀ i, μi i ≤ μ) (W : Matrix ζ ι ℝ)
    (hrelations : ∀ k s, MeasurableSet s →
      ∑ i, W k i * (μi i).real s = 0) :
    ∀ᵐ x ∂μ, W *ᵥ realDensity μ μi x = 0 := by
  have ha := realDensity_integrable μ μi
  have hrows : ∀ k, (fun x => ∑ i, W k i * realDensity μ μi x i) =ᵐ[μ] 0 := by
    intro k
    have hi : Integrable (fun x => ∑ i, W k i * realDensity μ μi x i) μ :=
      integrable_finsetSum Finset.univ (fun i _ => (ha.eval i).const_mul (W k i))
    apply hi.ae_eq_zero_of_forall_setIntegral_eq_zero
    intro s hs _
    rw [integral_finsetSum Finset.univ
      (fun i _ => ((ha.eval i).const_mul (W k i)).integrableOn)]
    calc
      (∑ i, ∫ x in s, W k i * realDensity μ μi x i ∂μ) =
          ∑ i, W k i * (μi i).real s := by
        apply Finset.sum_congr rfl
        intro i _
        rw [integral_const_mul]
        congr 1
        exact Measure.setIntegral_toReal_rnDeriv (hdom i).absolutelyContinuous s
      _ = 0 := hrelations k s hs
  have hall : ∀ᵐ x ∂μ, ∀ k, ∑ i, W k i * realDensity μ μi x i = 0 :=
    (ae_all_iff).mpr hrows
  filter_upwards [hall] with x hx
  funext k
  exact hx k

/-- Equation (7) follows from actual finite positive measures, actual linear
relations on all measurable sets, and a finite generating description of the
nonnegative kernel cone. -/
theorem decompose_positive_measure_vector
    (μ : Measure Ω) (μi : ι → Measure Ω)
    [IsFiniteMeasure μ] [∀ i, IsFiniteMeasure (μi i)]
    (hdom : ∀ i, μi i ≤ μ)
    (W : Matrix ζ ι ℝ) (r : κ → ι → ℝ)
    (hr : ∀ e i, 0 ≤ r e i)
    (hspan : ∀ y : ι → ℝ, (∀ i, 0 ≤ y i) → W *ᵥ y = 0 →
      ∃ c : κ → ℝ, (∀ e, 0 ≤ c e) ∧ ∑ e, c e • r e = y)
    (hrelations : ∀ k s, MeasurableSet s →
      ∑ i, W k i * (μi i).real s = 0) :
    ∃ ν : κ → Measure Ω,
      (∀ e, IsFiniteMeasure (ν e)) ∧
      ∀ i, μi i = ∑ e, ENNReal.ofReal (r e i) • ν e := by
  have hkernel := realDensity_linear_relations μ μi hdom W hrelations
  have hcone : ∀ᵐ x ∂μ, ∃ c : κ → ℝ, (∀ e, 0 ≤ c e) ∧
      ∑ e, c e • r e = realDensity μ μi x := by
    filter_upwards [hkernel] with x hx
    exact hspan _ (fun i => ENNReal.toReal_nonneg) hx
  obtain ⟨ν,hν,hdecomp⟩ := decompose_density μ r hr (realDensity μ μi)
    (realDensity_measurable μ μi) (realDensity_integrable μ μi) hcone
  refine ⟨ν,hν,?_⟩
  intro i
  rw [← realDensity_reconstructs μ μi hdom i]
  exact hdecomp i

end VolumeVerification.ConeMeasureDecomposition


module

public import PaperVerification.DnGaussian
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.MeasureTheory.Measure.Filter

@[expose] public section
/-! # Positive Gaussian mixtures, with no σ-finiteness assumption

The nonnegative Tonelli argument is a countable-sum monotone convergence theorem,
so the mixing measure may be arbitrary.  Finiteness at one common minimum is
enough: other points may have infinite energy, as happens for singular potentials.
A real-valued bridge recovers the literal convergent sum of integral potentials.
-/

noncomputable section

namespace PaperVerification.PositiveMixtures

open MeasureTheory Set Filter
open scoped ENNReal

abbrev PositiveParameter := Set.Ioi (0 : ℝ)

variable {ι X : Type*}

def gaussianDistanceSum (d : ι → X → ℝ) (α : PositiveParameter) (x : X) : ℝ :=
  ∑' v : ι, Real.exp (-(α : ℝ) * d v x)

def gaussianMixtureENNReal (ν : Measure PositiveParameter) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ α : PositiveParameter, ENNReal.ofReal (Real.exp (-(α : ℝ) * r)) ∂ν

/-- The literal nonnegative integral potential, whenever finite. -/
def gaussianMixture (ν : Measure PositiveParameter) (r : ℝ) : ℝ :=
  ∫ α : PositiveParameter, Real.exp (-(α : ℝ) * r) ∂ν

def mixtureEnergyENNReal (d : ι → X → ℝ) (ν : Measure PositiveParameter) (x : X) : ℝ≥0∞ :=
  ∑' v : ι, gaussianMixtureENNReal ν (d v x)

/-- The real series of the actual integral potentials. -/
def mixtureEnergy (d : ι → X → ℝ) (ν : Measure PositiveParameter) (x : X) : ℝ :=
  ∑' v : ι, gaussianMixture ν (d v x)

theorem measurable_gaussian_term (r : ℝ) :
    Measurable (fun α : PositiveParameter => ENNReal.ofReal (Real.exp (-(α : ℝ) * r))) := by
  exact (Real.continuous_exp.comp ((continuous_subtype_val.neg).mul_const r)).measurable.ennreal_ofReal

theorem gaussianMixture_eq_toReal (ν : Measure PositiveParameter) (r : ℝ) :
    gaussianMixture ν r = (gaussianMixtureENNReal ν r).toReal := by
  apply integral_eq_lintegral_of_nonneg_ae
  · exact Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le)
  · exact (Real.continuous_exp.comp ((continuous_subtype_val.neg).mul_const r)).aestronglyMeasurable

/-- One convergent, everywhere positive Gaussian already forces the index set
of lattice points to be countable. -/
theorem countable_of_gaussian_summable (d : ι → X → ℝ) (α : PositiveParameter) (x : X)
    (h : Summable (fun v : ι => Real.exp (-(α : ℝ) * d v x))) : Countable ι := by
  have hs := h.countable_support
  have he : Function.support (fun v : ι => Real.exp (-(α : ℝ) * d v x)) = univ := by
    ext v
    simp [Function.mem_support, (Real.exp_pos _).ne']
  rw [he] at hs
  exact Set.countable_univ_iff.mp hs

/-- Monotone convergence for a countable sum is the complete Tonelli step here. -/
theorem mixtureEnergy_tonelli [Countable ι] (d : ι → X → ℝ) (ν : Measure PositiveParameter)
    (hs : ∀ α : PositiveParameter, ∀ x, Summable (fun v : ι => Real.exp (-(α : ℝ) * d v x)))
    (x : X) :
    mixtureEnergyENNReal d ν x =
      ∫⁻ α : PositiveParameter, ENNReal.ofReal (gaussianDistanceSum d α x) ∂ν := by
  unfold mixtureEnergyENNReal gaussianMixtureENNReal gaussianDistanceSum
  rw [← lintegral_tsum (fun v => (measurable_gaussian_term (d v x)).aemeasurable)]
  apply lintegral_congr
  intro α
  exact (ENNReal.ofReal_tsum_of_nonneg (fun _ => (Real.exp_pos _).le) (hs α x)).symm

theorem measurable_gaussianDistanceSum [Countable ι] (d : ι → X → ℝ)
    (hs : ∀ α : PositiveParameter, ∀ x, Summable (fun v : ι => Real.exp (-(α : ℝ) * d v x)))
    (x : X) : Measurable (fun α => ENNReal.ofReal (gaussianDistanceSum d α x)) := by
  have he : (fun α : PositiveParameter => ENNReal.ofReal (gaussianDistanceSum d α x)) =
      fun α : PositiveParameter => ∑' v : ι,
        ENNReal.ofReal (Real.exp (-(α : ℝ) * d v x)) := by
    funext α
    exact ENNReal.ofReal_tsum_of_nonneg (fun _ => (Real.exp_pos _).le) (hs α x)
  rw [he]
  exact Measurable.ennreal_tsum (fun v => measurable_gaussian_term (d v x))

/-- Strict integration against an arbitrary nonzero positive measure.  Only the
smaller integral must be finite; the larger one may be infinite. -/
theorem lintegral_strict_of_pointwise_strict {A : Type*} [MeasurableSpace A]
    (ν : Measure A) (hν : ν ≠ 0) {f g : A → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hfg : ∀ a, f a < g a)
    (hfin : (∫⁻ a, f a ∂ν) ≠ ∞) :
    (∫⁻ a, f a ∂ν) < ∫⁻ a, g a ∂ν := by
  let h : A → ℝ≥0∞ := fun a => g a - f a
  have hm : Measurable h := hg.sub hf
  have hp (a : A) : 0 < h a := tsub_pos_iff_lt.mpr (hfg a)
  have hne : (∫⁻ a, h a ∂ν) ≠ 0 := by
    intro hzero
    have hae := (lintegral_eq_zero_iff hm).mp hzero
    letI : (ae ν).NeBot := ae_neBot.mpr hν
    obtain ⟨a, ha⟩ := hae.exists
    exact (hp a).ne' ha
  have he : (fun a => f a + h a) = g := by
    funext a
    exact add_tsub_cancel_of_le (hfg a).le
  rw [← he, lintegral_add_left hf]
  exact ENNReal.lt_add_right hfin hne

/-- Strictness at every positive parameter follows from the exact common
minimum set, not from a separate assumption about the potential. -/
theorem gaussian_strict_off_common_minimum (d : ι → X → ℝ) (H : X → Prop)
    (hmain : ∀ α : PositiveParameter, ∀ x,
      (∀ y, gaussianDistanceSum d α x ≤ gaussianDistanceSum d α y) ↔ H x)
    {c x : X} (hc : H c) (hx : ¬H x) (α : PositiveParameter) :
    gaussianDistanceSum d α c < gaussianDistanceSum d α x := by
  have hmin := (hmain α c).mpr hc
  have hle := hmin x
  apply lt_of_le_of_ne hle
  intro heq
  have hxMin : ∀ y, gaussianDistanceSum d α x ≤ gaussianDistanceSum d α y := by
    intro y
    rw [← heq]
    exact hmin y
  exact hx ((hmain α x).mp hxMin)

/-- Corollary 1.2's complete transfer principle.  Countability is derived from
Gaussian convergence, and no finite or σ-finite measure assumption is imposed.
Finiteness at one common minimum permits singular potentials elsewhere. -/
theorem gaussian_mixture_minimizers (d : ι → X → ℝ) (H : X → Prop)
    (ν : Measure PositiveParameter) (hν : ν ≠ 0)
    (hs : ∀ α : PositiveParameter, ∀ x, Summable (fun v : ι => Real.exp (-(α : ℝ) * d v x)))
    (hmain : ∀ α : PositiveParameter, ∀ x,
      (∀ y, gaussianDistanceSum d α x ≤ gaussianDistanceSum d α y) ↔ H x)
    (c : X) (hc : H c) (hfin : mixtureEnergyENNReal d ν c ≠ ∞) (x : X) :
    (∀ y, mixtureEnergyENNReal d ν x ≤ mixtureEnergyENNReal d ν y) ↔ H x := by
  letI : Countable ι := countable_of_gaussian_summable d ⟨1, by norm_num⟩ c (hs _ c)
  constructor
  · intro hmin
    by_contra hx
    have hpoint (α : PositiveParameter) : ENNReal.ofReal (gaussianDistanceSum d α c) <
        ENNReal.ofReal (gaussianDistanceSum d α x) := by
      apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (tsum_nonneg fun _ => (Real.exp_pos _).le)).mpr
      exact gaussian_strict_off_common_minimum d H hmain hc hx α
    have hfin' : (∫⁻ α : PositiveParameter, ENNReal.ofReal (gaussianDistanceSum d α c) ∂ν) ≠ ∞ := by
      rwa [← mixtureEnergy_tonelli d ν hs]
    have hstrict := lintegral_strict_of_pointwise_strict ν hν
      (measurable_gaussianDistanceSum d hs c) (measurable_gaussianDistanceSum d hs x) hpoint hfin'
    rw [← mixtureEnergy_tonelli d ν hs c, ← mixtureEnergy_tonelli d ν hs x] at hstrict
    exact (not_lt_of_ge (hmin c)) hstrict
  · intro hx y
    rw [mixtureEnergy_tonelli d ν hs x, mixtureEnergy_tonelli d ν hs y]
    apply lintegral_mono
    intro α
    exact ENNReal.ofReal_le_ofReal ((hmain α x).mpr hx y)

/-- Convergence at any one ambient point already implies convergence at
every common Gaussian minimum. Thus a singular potential need not be
finite at lattice points or at any prescribed reference point. -/
theorem gaussian_mixture_minimizers_of_exists_finite (d : ι → X → ℝ) (H : X → Prop)
    (ν : Measure PositiveParameter) (hν : ν ≠ 0)
    (hs : ∀ α : PositiveParameter, ∀ x,
      Summable (fun v : ι => Real.exp (-(α : ℝ) * d v x)))
    (hmain : ∀ α : PositiveParameter, ∀ x,
      (∀ y, gaussianDistanceSum d α x ≤ gaussianDistanceSum d α y) ↔ H x)
    (c : X) (hc : H c) (hfin : ∃ y,mixtureEnergyENNReal d ν y≠∞) (x : X) :
    (∀ y,mixtureEnergyENNReal d ν x≤mixtureEnergyENNReal d ν y) ↔ H x := by
  obtain ⟨y,hy⟩ := hfin
  letI : Countable ι := countable_of_gaussian_summable d ⟨1,by norm_num⟩ c (hs _ c)
  have hle : mixtureEnergyENNReal d ν c≤mixtureEnergyENNReal d ν y := by
    rw [mixtureEnergy_tonelli d ν hs c,mixtureEnergy_tonelli d ν hs y]
    exact lintegral_mono (fun α=>ENNReal.ofReal_le_ofReal ((hmain α c).mpr hc y))
  exact gaussian_mixture_minimizers d H ν hν hs hmain c hc
    (ne_top_of_le_ne_top hy hle) x

theorem mixtureEnergy_eq_toReal (d : ι → X → ℝ) (ν : Measure PositiveParameter) (x : X)
    (hfin : mixtureEnergyENNReal d ν x ≠ ∞) :
    mixtureEnergy d ν x = (mixtureEnergyENNReal d ν x).toReal := by
  unfold mixtureEnergy mixtureEnergyENNReal at *
  simp_rw [gaussianMixture_eq_toReal]
  exact (ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top hfin)).symm

theorem summable_mixtureEnergy (d : ι → X → ℝ) (ν : Measure PositiveParameter) (x : X)
    (hfin : mixtureEnergyENNReal d ν x ≠ ∞) : Summable (fun v => gaussianMixture ν (d v x)) := by
  simp_rw [gaussianMixture_eq_toReal]
  exact ENNReal.summable_toReal hfin

/-- Finiteness of the nonnegative lattice energy makes every individual
integral potential genuinely integrable.  Thus the real-valued corollary
never relies on the default value of a nonintegrable Bochner integral. -/
theorem integrable_gaussian_term_of_energy_finite (d : ι → X → ℝ)
    (ν : Measure PositiveParameter) (x : X)
    (hfin : mixtureEnergyENNReal d ν x ≠ ∞) (v : ι) :
    Integrable (fun α : PositiveParameter => Real.exp (-(α : ℝ) * d v x)) ν := by
  change (∑' w : ι, gaussianMixtureENNReal ν (d w x)) ≠ ∞ at hfin
  have hv : gaussianMixtureENNReal ν (d v x) ≠ ∞ :=
    ENNReal.ne_top_of_tsum_ne_top hfin v
  exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
    (Real.continuous_exp.comp ((continuous_subtype_val.neg).mul_const (d v x))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)).mp hv

/-- Literal real-valued convergent lattice sums of the stated integral potential.
Every quantifier over ambient points remains unrestricted. -/
theorem gaussian_mixture_minimizers_real (d : ι → X → ℝ) (H : X → Prop)
    (ν : Measure PositiveParameter) (hν : ν ≠ 0)
    (hs : ∀ α : PositiveParameter, ∀ x, Summable (fun v : ι => Real.exp (-(α : ℝ) * d v x)))
    (hmain : ∀ α : PositiveParameter, ∀ x,
      (∀ y, gaussianDistanceSum d α x ≤ gaussianDistanceSum d α y) ↔ H x)
    (c : X) (hc : H c) (hfin : ∀ x, mixtureEnergyENNReal d ν x ≠ ∞) (x : X) :
    (∀ y, mixtureEnergy d ν x ≤ mixtureEnergy d ν y) ↔ H x := by
  have h := gaussian_mixture_minimizers d H ν hν hs hmain c hc (hfin c) x
  have he : (∀ y, mixtureEnergy d ν x ≤ mixtureEnergy d ν y) ↔
      ∀ y, mixtureEnergyENNReal d ν x ≤ mixtureEnergyENNReal d ν y := by
    constructor <;> intro hxy y
    · have hy := hxy y
      rw [mixtureEnergy_eq_toReal d ν x (hfin x), mixtureEnergy_eq_toReal d ν y (hfin y)] at hy
      exact (ENNReal.toReal_le_toReal (hfin x) (hfin y)).mp hy
    · rw [mixtureEnergy_eq_toReal d ν x (hfin x), mixtureEnergy_eq_toReal d ν y (hfin y)]
      exact (ENNReal.toReal_le_toReal (hfin x) (hfin y)).mpr (hxy y)
  exact he.trans h

/-- Finiteness of the nonnegative energy is exactly the ordinary convergence
condition for the integral potential and its lattice sum. -/
theorem mixtureEnergyENNReal_ne_top_iff_integrable_summable
    (d : ι → X → ℝ) (ν : Measure PositiveParameter) (x : X) :
    mixtureEnergyENNReal d ν x ≠ ∞ ↔
      (∀ v : ι, Integrable
        (fun α : PositiveParameter => Real.exp (-(α : ℝ) * d v x)) ν) ∧
      Summable (fun v : ι => gaussianMixture ν (d v x)) := by
  constructor
  · intro hfin
    exact ⟨integrable_gaussian_term_of_energy_finite d ν x hfin,
      summable_mixtureEnergy d ν x hfin⟩
  · rintro ⟨hint, hsum⟩
    have he (v : ι) : gaussianMixtureENNReal ν (d v x) =
        ENNReal.ofReal (gaussianMixture ν (d v x)) := by
      exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hint v)
        (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))).symm
    unfold mixtureEnergyENNReal
    simp_rw [he]
    exact hsum.tsum_ofReal_ne_top

/-- The hypothesis in the real-valued corollary is equivalent to pointwise
integrability of the stated potential and ordinary convergence at every point. -/
theorem mixtureEnergyENNReal_everywhere_finite_iff
    (d : ι → X → ℝ) (ν : Measure PositiveParameter) :
    (∀ x : X, mixtureEnergyENNReal d ν x ≠ ∞) ↔
      (∀ x : X, ∀ v : ι, Integrable
        (fun α : PositiveParameter => Real.exp (-(α : ℝ) * d v x)) ν) ∧
      (∀ x : X, Summable (fun v : ι => gaussianMixture ν (d v x))) := by
  constructor
  · intro h
    exact ⟨fun x => ((mixtureEnergyENNReal_ne_top_iff_integrable_summable d ν x).mp
      (h x)).1, fun x => ((mixtureEnergyENNReal_ne_top_iff_integrable_summable d ν x).mp
      (h x)).2⟩
  · rintro ⟨hint, hsum⟩ x
    exact (mixtureEnergyENNReal_ne_top_iff_integrable_summable d ν x).mpr
      ⟨hint x, hsum x⟩


end PaperVerification.PositiveMixtures

#print axioms PaperVerification.PositiveMixtures.gaussian_mixture_minimizers
#print axioms PaperVerification.PositiveMixtures.gaussian_mixture_minimizers_real
#print axioms PaperVerification.PositiveMixtures.mixtureEnergyENNReal_ne_top_iff_integrable_summable
#print axioms PaperVerification.PositiveMixtures.mixtureEnergyENNReal_everywhere_finite_iff

module

public import Ellipsoid.PowerTilts
public import Ellipsoid.IntegralGram
public import Ellipsoid.OrderedMinKernel

@[expose] public section

noncomputable section

open MeasureTheory Set Matrix
open scoped BigOperators ENNReal

namespace EllipsoidVerification

theorem integrable_tail_mellin_and_integral
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsFiniteMeasure ν]
    (X : Ω → ℝ) (hXm : Measurable X) (hX0 : ∀ x, 0 ≤ X x)
    {r : ℝ} (hr : 0 < r) (hXi : Integrable (fun x => X x ^ r) ν) :
    IntegrableOn (fun s : ℝ => s ^ (r - 1) * (ν {x | s < X x}).toReal) (Ioi 0) ∧
      (∫ s in Ioi (0 : ℝ), s ^ (r - 1) * (ν {x | s < X x}).toReal) =
        (∫ x, X x ^ r ∂ν) / r := by
  let q : ℝ → ℝ := fun s => (ν {x | s < X x}).toReal
  have hq : Antitone q := by
    intro s t hst
    exact ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono fun x hx => lt_of_le_of_lt hst hx)
  have hqm : Measurable q := hq.measurable
  let H : ℝ → ℝ := fun s => s ^ (r - 1) * q s
  have hHm : Measurable H := (measurable_id.pow_const _).mul hqm
  have hH0 : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] H := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact mul_nonneg (Real.rpow_nonneg hs.le _) ENNReal.toReal_nonneg
  have heq : (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (H s)) =
      ∫⁻ s in Ioi (0 : ℝ), ν {x | s < X x} * ENNReal.ofReal (s ^ (r - 1)) := by
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    dsimp only [H, q]
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _),
      ENNReal.ofReal_toReal (measure_ne_top _ _), mul_comm]
  have hLayer := lintegral_rpow_eq_lintegral_meas_lt_mul ν (ae_of_all _ hX0)
    hXm.aemeasurable hr
  rw [← heq] at hLayer
  have hfinite : (∫⁻ x, ENNReal.ofReal (X x ^ r) ∂ν) ≠ ∞ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hXi (ae_of_all _ fun x =>
      Real.rpow_nonneg (hX0 x) r)]
    exact ENNReal.ofReal_ne_top
  have hHfinite : (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (H s)) ≠ ∞ := by
    intro htop
    rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hr).ne'] at hLayer
    exact hfinite hLayer
  have hHi : Integrable H (volume.restrict (Ioi (0 : ℝ))) :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hHm.aestronglyMeasurable hH0).mp hHfinite
  refine ⟨hHi, ?_⟩
  have hReal := congrArg ENNReal.toReal hLayer
  rw [← integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x =>
    Real.rpow_nonneg (hX0 x) r) hXi.aestronglyMeasurable,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hr.le,
    ← integral_eq_lintegral_of_nonneg_ae hH0 hHm.aestronglyMeasurable] at hReal
  exact (eq_div_iff hr.ne').mpr (by simpa only [mul_comm] using hReal.symm)

theorem reciprocalTail_mellin {μ : Measure PositiveLine} (hμ : μ ≠ 0)
    {a r : ℝ} (hr : 0 < r)
    (ha : Integrable (fun t : PositiveLine => (t.val : ℝ) ^ a) μ)
    (har : Integrable (fun t : PositiveLine => (t.val : ℝ) ^ (a - r)) μ) :
    IntegrableOn (fun s : ℝ => s ^ (r - 1) * reciprocalTail μ a s) (Ioi 0) ∧
      (∫ s in Ioi (0 : ℝ), s ^ (r - 1) * reciprocalTail μ a s) =
        positiveMoment μ (a - r) / (r * positiveMoment μ a) := by
  letI := powerTilt_probability hμ ha
  have hpow : Integrable (fun t : PositiveLine => (t.val : ℝ) ^ (-r)) (powerTilt μ a) := by
    apply integrable_powerTilt_power hμ ha
    simpa only [sub_eq_add_neg] using har
  have hi : Integrable (fun t : PositiveLine => ((t.val : ℝ)⁻¹) ^ r) (powerTilt μ a) := by
    convert hpow using 1
    funext t
    rw [Real.inv_rpow t.property.le, Real.rpow_neg t.property.le]
  obtain ⟨hInt, hval⟩ := integrable_tail_mellin_and_integral (powerTilt μ a)
    (fun t : PositiveLine => (t.val : ℝ)⁻¹) (by fun_prop)
    (fun t => inv_nonneg.mpr t.property.le) hr hi
  refine ⟨hInt, ?_⟩
  change (∫ s in Ioi (0 : ℝ), s ^ (r - 1) *
    ((powerTilt μ a) {t | s < (t.val : ℝ)⁻¹}).toReal) = _
  rw [hval, integral_powerTilt ha]
  have heq : (fun t : PositiveLine => (t.val : ℝ) ^ a * ((t.val : ℝ)⁻¹) ^ r) =
      (fun t : PositiveLine => (t.val : ℝ) ^ (a - r)) := by
    funext t
    rw [Real.inv_rpow t.property.le, ← Real.rpow_neg t.property.le,
      ← Real.rpow_add t.property, sub_eq_add_neg]
  rw [heq]
  dsimp [positiveMoment]
  ring

def orderedMomentGram (μ : Measure PositiveLine) {ι : Type*} (p : ι → ℝ) :
    Matrix ι ι ℝ :=
  fun i j => positiveMoment μ (2 * max (p i) (p j) - min (p i) (p j)) /
    ((p i + p j) * positiveMoment μ (3 * max (p i) (p j)))

def orderedMomentKernel (μ : Measure PositiveLine) {ι : Type*} (p : ι → ℝ) :
    Matrix ι ι ℝ := fun i j =>
      min (p i) (p j) * positiveMoment μ (3 * min (p i) (p j)) *
        positiveMoment μ (2 * max (p i) (p j) - min (p i) (p j))

theorem orderedMomentGram_posSemidef {μ : Measure PositiveLine} [SFinite μ]
    (hμ : μ ≠ 0) {m : ℕ} {p : Fin m → ℝ}
    (hp : StrictMono p) (hp0 : ∀ i, 0 < p i)
    (h3 : ∀ i, Integrable (fun t : PositiveLine => (t.val : ℝ) ^ (3 * p i)) μ)
    (hm : ∀ i j, i ≤ j → Integrable
      (fun t : PositiveLine => (t.val : ℝ) ^ (2 * p j - p i)) μ) :
    (orderedMomentGram μ p).PosSemidef := by
  let A : ℝ → Matrix (Fin m) (Fin m) ℝ := fun s i j =>
    s ^ (p i - 1 / 2) * s ^ (p j - 1 / 2) *
      min (reciprocalTail μ (3 * p i) s) (reciprocalTail μ (3 * p j) s)
  have hA : ∀ s : ℝ, (A s).PosSemidef := by
    intro s
    exact weighted_minKernel_posSemidef (fun i => reciprocalTail μ (3 * p i) s)
      (fun i => s ^ (p i - 1 / 2)) (fun i => reciprocalTail_nonneg _ _ _)
  have hentry (i j : Fin m) :
      (fun s => A s i j) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun s => s ^ (p i + p j - 1) * reciprocalTail μ (3 * max (p i) (p j)) s) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    dsimp [A]
    rw [← Real.rpow_add hs]
    have hexp : p i - 1 / 2 + (p j - 1 / 2) = p i + p j - 1 := by ring
    rw [hexp]
    rcases le_total i j with hij | hji
    · rw [max_eq_right (hp.monotone hij), min_eq_right
        (reciprocalTail_antitone_exponent hμ (by linarith [hp.monotone hij]) (h3 i) (h3 j) s)]
    · rw [max_eq_left (hp.monotone hji), min_eq_left
        (reciprocalTail_antitone_exponent hμ (by linarith [hp.monotone hji]) (h3 j) (h3 i) s)]
  have htail (i j : Fin m) :
      IntegrableOn (fun s : ℝ => s ^ (p i + p j - 1) *
        reciprocalTail μ (3 * max (p i) (p j)) s) (Ioi 0) ∧
      (∫ s in Ioi (0 : ℝ), s ^ (p i + p j - 1) *
        reciprocalTail μ (3 * max (p i) (p j)) s) = orderedMomentGram μ p i j := by
    rcases le_total i j with hij | hji
    · have he : 3 * p j - (p i + p j) = 2 * p j - p i := by ring
      simpa only [max_eq_right (hp.monotone hij), min_eq_left (hp.monotone hij),
        he, orderedMomentGram] using reciprocalTail_mellin hμ (add_pos (hp0 i) (hp0 j))
          (h3 j) (by simpa only [he] using hm i j hij)
    · have he : 3 * p i - (p i + p j) = 2 * p i - p j := by ring
      simpa only [max_eq_left (hp.monotone hji), min_eq_right (hp.monotone hji),
        he, orderedMomentGram] using reciprocalTail_mellin hμ (add_pos (hp0 i) (hp0 j))
          (h3 i) (by simpa only [he] using hm j i hji)
  have hi (i j : Fin m) : Integrable (fun s => A s i j) (volume.restrict (Ioi (0 : ℝ))) :=
    (htail i j).1.congr (hentry i j).symm
  have h := integral_matrix_posSemidef (volume.restrict (Ioi (0 : ℝ))) A
    (ae_of_all _ hA) hi
  have hmat : ((fun i j => ∫ s in Ioi (0 : ℝ), A s i j) :
      Matrix (Fin m) (Fin m) ℝ) = orderedMomentGram μ p := by
    ext i j
    rw [integral_congr_ae (hentry i j), (htail i j).2]
  rw [hmat] at h
  exact h

theorem orderedMomentGram_diagonal_pos {μ : Measure PositiveLine} (hμ : μ ≠ 0)
    {m : ℕ} {p : Fin m → ℝ} (hp0 : ∀ i, 0 < p i)
    (h3 : ∀ i, Integrable (fun t : PositiveLine => (t.val : ℝ) ^ (3 * p i)) μ)
    (hm : ∀ i, Integrable (fun t : PositiveLine => (t.val : ℝ) ^ p i) μ) (i : Fin m) :
    0 < orderedMomentGram μ p i i := by
  simp only [orderedMomentGram, min_self, max_self, show 2 * p i - p i = p i by ring]
  exact div_pos (positiveMoment_pos hμ (hm i))
    (mul_pos (add_pos (hp0 i) (hp0 i)) (positiveMoment_pos hμ (h3 i)))

end EllipsoidVerification

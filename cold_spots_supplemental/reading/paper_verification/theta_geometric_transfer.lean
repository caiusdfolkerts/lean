module
public import PaperVerification.ThetaHyperbolicArc
public import PaperVerification.GeometricMeanLaws
public import PaperVerification.HyperbolicMeasure
@[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

open MeasureTheory Set Filter Topology
open PaperVerification.Hyperbolic

abbrev HalfInterval := Set.Icc (0 : ℝ) (1 / 2)

def thetaAMap {α : ℝ} (hα : 0 < α) : C(HalfInterval, ℝ) :=
  ⟨fun t ↦ gaussian α t, (continuous_gaussian hα).comp continuous_subtype_val⟩

def thetaBMap {α : ℝ} (hα : 0 < α) : C(HalfInterval, ℝ) :=
  ⟨fun t ↦ alternatingGaussian α t, (continuous_alternatingGaussian hα).comp continuous_subtype_val⟩

def thetaCMap {α : ℝ} (hα : 0 < α) : C(HalfInterval, ℝ) :=
  ⟨fun t ↦ gaussian α ((t : ℝ) - 1 / 2),
    (continuous_gaussian hα).comp (continuous_subtype_val.sub continuous_const)⟩

def thetaDMap {α : ℝ} (hα : 0 < α) : C(HalfInterval, ℝ) :=
  ⟨fun t ↦ alternatingGaussian α ((t : ℝ) - 1 / 2),
    (continuous_alternatingGaussian hα).comp (continuous_subtype_val.sub continuous_const)⟩

def thetaRootMap {α : ℝ} (hα : 0 < α) : C(HalfInterval, ℝ) :=
  ⟨fun t ↦ Real.sqrt (thetaScale α t),
    Real.continuous_sqrt.comp ((continuous_thetaScale hα).comp continuous_subtype_val)⟩

def thetaArcMap {α : ℝ} (hα : 0 < α) : C(HalfInterval, Interval (thetaR α)) :=
  ⟨thetaArcPoint hα, continuous_thetaArcPoint hα⟩

def thetaDiagonalMap {α : ℝ} (hα : 0 < α) : C(HalfInterval, ℝ) :=
  ⟨thetaDiagonal α ∘ Subtype.val, by
    exact continuous_const.mul
      (((((thetaAMap hα).continuous.pow 8).add ((thetaCMap hα).continuous.pow 8)).sub
        ((thetaBMap hα).continuous.pow 8)).sub ((thetaDMap hα).continuous.pow 8))⟩

def centeredCoshMap (R : ℝ) : C(Interval R, ℝ) :=
  ⟨fun p ↦ Real.cosh (2 * (p : ℝ) - R),
    Real.continuous_cosh.comp
      ((continuous_const.mul continuous_subtype_val).sub continuous_const)⟩

def thetaPush {α : ℝ} (hα : 0 < α) (μ : ProbabilityMeasure HalfInterval) :
    ProbabilityMeasure (Interval (thetaR α)) := μ.map (thetaArcMap hα)

lemma thetaAMap_pos {α : ℝ} (hα : 0 < α) (t : HalfInterval) : 0 < thetaAMap hα t :=
  gaussian_pos hα t

lemma thetaBMap_nonneg {α : ℝ} (hα : 0 < α) (t : HalfInterval) : 0 ≤ thetaBMap hα t :=
  alternatingGaussian_nonneg hα t.property.1 t.property.2

lemma thetaCMap_pos {α : ℝ} (hα : 0 < α) (t : HalfInterval) : 0 < thetaCMap hα t :=
  gaussian_pos hα _

lemma thetaDMap_nonneg {α : ℝ} (hα : 0 < α) (t : HalfInterval) : 0 ≤ thetaDMap hα t := by
  change 0 ≤ alternatingGaussian α ((t : ℝ) - 1 / 2)
  rw [show (t : ℝ) - 1 / 2 = -(1 / 2 - (t : ℝ)) by ring, alternatingGaussian_even]
  exact alternatingGaussian_nonneg hα (by linarith [t.property.2])
    (by linarith [t.property.1])

lemma thetaRootMap_pos {α : ℝ} (hα : 0 < α) (t : HalfInterval) :
    0 < thetaRootMap hα t := Real.sqrt_pos.mpr (thetaScale_pos hα t)

lemma thetaAMap_square {α : ℝ} (hα : 0 < α) :
    thetaAMap hα ^ 2 = (intervalCosh (thetaR α)).comp (thetaArcMap hα) * thetaRootMap hα := by
  ext t
  change gaussian α t ^ 2 = Real.cosh (thetaP α t) * Real.sqrt (thetaScale α t)
  exact ((eq_div_iff (Real.sqrt_pos.mpr (thetaScale_pos hα t)).ne').mp (thetaP_cosh hα t)).symm

lemma thetaBMap_square {α : ℝ} (hα : 0 < α) :
    thetaBMap hα ^ 2 = (intervalSinh (thetaR α)).comp (thetaArcMap hα) * thetaRootMap hα := by
  ext t
  change alternatingGaussian α t ^ 2 = Real.sinh (thetaP α t) * Real.sqrt (thetaScale α t)
  exact ((eq_div_iff (Real.sqrt_pos.mpr (thetaScale_pos hα t)).ne').mp (thetaP_sinh α t)).symm

lemma thetaCMap_square {α : ℝ} (hα : 0 < α) :
    thetaCMap hα ^ 2 =
      (intervalReflectedCosh (thetaR α)).comp (thetaArcMap hα) * thetaRootMap hα := by
  ext t
  change gaussian α ((t : ℝ) - 1 / 2) ^ 2 =
    Real.cosh (thetaR α - thetaP α t) * Real.sqrt (thetaScale α t)
  exact ((eq_div_iff (Real.sqrt_pos.mpr (thetaScale_pos hα t)).ne').mp
    (thetaP_cosh_sub hα t)).symm

lemma thetaDMap_square {α : ℝ} (hα : 0 < α) :
    thetaDMap hα ^ 2 =
      (intervalReflectedSinh (thetaR α)).comp (thetaArcMap hα) * thetaRootMap hα := by
  ext t
  change alternatingGaussian α ((t : ℝ) - 1 / 2) ^ 2 =
    Real.sinh (thetaR α - thetaP α t) * Real.sqrt (thetaScale α t)
  exact ((eq_div_iff (Real.sqrt_pos.mpr (thetaScale_pos hα t)).ne').mp
    (thetaP_sinh_sub hα t)).symm

lemma hyperbolic_half_diagonal (R p : ℝ) :
    Real.cosh p ^ 2 + Real.sinh (R - p) ^ 2 =
      Real.cosh R * Real.cosh (2 * p - R) := by
  have h₁ := Real.cosh_add R (2 * p - R)
  have h₂ := Real.cosh_sub R (2 * p - R)
  rw [show R + (2 * p - R) = 2 * p by ring] at h₁
  rw [show R - (2 * p - R) = 2 * (R - p) by ring] at h₂
  rw [Real.cosh_two_mul] at h₁ h₂
  nlinarith [Real.cosh_sq_sub_sinh_sq p, Real.cosh_sq_sub_sinh_sq (R - p)]

theorem thetaDiagonal_hyperbolic {α : ℝ} (hα : 0 < α) (t : ℝ) :
    thetaDiagonal α t = thetaScale α t ^ 2 * Real.cosh (thetaR α) *
      Real.cosh (2 * thetaP α t - thetaR α) := by
  have hr : Real.sqrt (thetaScale α t) ≠ 0 := (Real.sqrt_pos.mpr (thetaScale_pos hα t)).ne'
  have hA := ((eq_div_iff hr).mp (thetaP_cosh hα t)).symm
  have hD := ((eq_div_iff hr).mp (thetaP_sinh_sub hα t)).symm
  calc
    thetaDiagonal α t = thetaScale α t *
        (gaussian α t ^ 4 + alternatingGaussian α (t - 1 / 2) ^ 4) := thetaDiagonal_scale hα t
    _ = thetaScale α t * (Real.sqrt (thetaScale α t) ^ 2 *
        (Real.cosh (thetaP α t) ^ 2 + Real.sinh (thetaR α - thetaP α t) ^ 2)) := by
      rw [show gaussian α t ^ 4 = (gaussian α t ^ 2) ^ 2 by ring,
        show alternatingGaussian α (t - 1 / 2) ^ 4 =
          (alternatingGaussian α (t - 1 / 2) ^ 2) ^ 2 by ring, hA, hD]
      ring
    _ = _ := by
      rw [Real.sq_sqrt (thetaScale_pos hα t).le, hyperbolic_half_diagonal]
      ring

def thetaNormalization {α : ℝ} (hα : 0 < α) (μ : ProbabilityMeasure HalfInterval) : ℝ :=
  geometricMoment 4 (thetaRootMap hα) μ

def thetaMomentNumerator {α : ℝ} (hα : 0 < α) (μ : ProbabilityMeasure HalfInterval) : ℝ :=
  geometricMoment 8 (thetaAMap hα) μ + geometricMoment 8 (thetaCMap hα) μ -
    geometricMoment 8 (thetaBMap hα) μ - geometricMoment 8 (thetaDMap hα) μ

theorem thetaNormalization_pos {α : ℝ} (hα : 0 < α) (μ : ProbabilityMeasure HalfInterval) :
    0 < thetaNormalization hα μ :=
  geometricMoment_pos_of_pos 4 (by norm_num) (thetaRootMap hα) μ (thetaRootMap_pos hα)

lemma theta_moment_factorization {α : ℝ} (hα : 0 < α) (μ : ProbabilityMeasure HalfInterval)
    (f : C(HalfInterval, ℝ)) (F : C(Interval (thetaR α), ℝ))
    (hf : ∀ t, 0 ≤ f t) (hF : ∀ t, 0 ≤ F t)
    (heq : f ^ 2 = F.comp (thetaArcMap hα) * thetaRootMap hα) :
    geometricMoment 8 f μ = thetaNormalization hα μ * geometricMoment 4 F (thetaPush hα μ) := by
  have hp := geometricMoment_nat_pow 4 2 f μ hf
  norm_num only [Nat.reduceMul, Nat.cast_ofNat] at hp
  rw [← hp, heq,
    geometricMoment_mul_pos_right 4 (by norm_num) _ _ μ
      (fun t ↦ hF (thetaArcMap hα t)) (thetaRootMap_pos hα),
    ← geometricMoment_map]
  unfold thetaNormalization thetaPush
  ring

theorem thetaMomentNumerator_factorization {α : ℝ} (hα : 0 < α)
    (μ : ProbabilityMeasure HalfInterval) :
    thetaMomentNumerator hα μ =
      thetaNormalization hα μ * hyperbolicNumerator (thetaR α) (thetaPush hα μ) := by
  have hA := theta_moment_factorization hα μ (thetaAMap hα) (intervalCosh (thetaR α))
    (fun t ↦ (thetaAMap_pos hα t).le) (fun p ↦ (Real.cosh_pos (p : ℝ)).le) (thetaAMap_square hα)
  have hB := theta_moment_factorization hα μ (thetaBMap hα) (intervalSinh (thetaR α))
    (thetaBMap_nonneg hα) (fun p ↦ Real.sinh_nonneg_iff.mpr p.property.1) (thetaBMap_square hα)
  have hC := theta_moment_factorization hα μ (thetaCMap hα) (intervalReflectedCosh (thetaR α))
    (fun t ↦ (thetaCMap_pos hα t).le) (fun p ↦ (Real.cosh_pos _).le) (thetaCMap_square hα)
  have hD := theta_moment_factorization hα μ (thetaDMap hα) (intervalReflectedSinh (thetaR α))
    (thetaDMap_nonneg hα) (fun p ↦ Real.sinh_nonneg_iff.mpr (sub_nonneg.mpr p.property.2))
    (thetaDMap_square hα)
  unfold thetaMomentNumerator hyperbolicNumerator
  rw [hA, hB, hC, hD]
  ring

lemma thetaDiagonalMap_factorization {α : ℝ} (hα : 0 < α) :
    thetaDiagonalMap hα = thetaRootMap hα ^ 4 *
      (ContinuousMap.const HalfInterval (Real.cosh (thetaR α)) *
        (centeredCoshMap (thetaR α)).comp (thetaArcMap hα)) := by
  ext t
  change thetaDiagonal α t = Real.sqrt (thetaScale α t) ^ 4 *
    (Real.cosh (thetaR α) * Real.cosh (2 * thetaP α t - thetaR α))
  rw [thetaDiagonal_hyperbolic hα,
    show Real.sqrt (thetaScale α t) ^ 4 = (Real.sqrt (thetaScale α t) ^ 2) ^ 2 by ring,
    Real.sq_sqrt (thetaScale_pos hα t).le]
  ring

theorem thetaDiagonal_geometric_factorization {α : ℝ} (hα : 0 < α)
    (μ : ProbabilityMeasure HalfInterval) :
    geometricMean (thetaDiagonalMap hα) μ = thetaNormalization hα μ * Real.cosh (thetaR α) *
      geometricMean (centeredCoshMap (thetaR α)) (thetaPush hα μ) := by
  have hroot : geometricMean (thetaRootMap hα) μ ^ 4 = thetaNormalization hα μ :=
    (geometricMoment_nat 4 (thetaRootMap hα) μ).symm
  have hmap : geometricMean (centeredCoshMap (thetaR α)) (thetaPush hα μ) =
      geometricMean ((centeredCoshMap (thetaR α)).comp (thetaArcMap hα)) μ :=
    geometricMoment_map 1 (centeredCoshMap (thetaR α)) (thetaArcMap hα) μ
  rw [thetaDiagonalMap_factorization hα,
    geometricMean_mul_pos_right _ _ μ (fun t ↦ pow_nonneg (thetaRootMap_pos hα t).le 4)
      (fun t ↦ mul_pos (Real.cosh_pos _) (Real.cosh_pos _)),
    geometricMean_pow 4 _ μ (fun t ↦ (thetaRootMap_pos hα t).le),
    geometricMean_mul_pos_right _ _ μ (fun _ ↦ (Real.cosh_pos _).le)
      (fun _ ↦ Real.cosh_pos _),
    geometricMean_const (Real.cosh_pos _) μ, hroot, ← hmap]
  ring

theorem thetaDiagonal_geometric_lower {α : ℝ} (hα : 0 < α)
    (μ : ProbabilityMeasure HalfInterval) :
    (gaussian α 0 * gaussian α (1 / 2)) ^ 4 ≤ geometricMean (thetaDiagonalMap hα) μ :=
  geometricMean_ge_const (thetaDiagonalMap hα) μ
    (pow_pos (mul_pos (gaussian_pos hα 0) (gaussian_pos hα (1 / 2))) 4)
    (fun t ↦ thetaDiagonal_min hα t)

/-- The diagonal equality condition is exact for every probability measure. -/
theorem thetaDiagonal_geometric_eq_iff {α : ℝ} (hα : 0 < α)
    (μ : ProbabilityMeasure HalfInterval) :
    geometricMean (thetaDiagonalMap hα) μ = (gaussian α 0 * gaussian α (1 / 2)) ^ 4 ↔
      ∀ᵐ (t : HalfInterval) ∂(μ : Measure HalfInterval),
        (t : ℝ) = 0 ∨ (t : ℝ) = 1 / 4 ∨ (t : ℝ) = 1 / 2 := by
  rw [geometricMean_eq_const_iff (thetaDiagonalMap hα) μ
    (pow_pos (mul_pos (gaussian_pos hα 0) (gaussian_pos hα (1 / 2))) 4)
    (fun t ↦ thetaDiagonal_min hα t)]
  constructor
  · intro h
    filter_upwards [h] with t ht
    exact (thetaDiagonal_equality_points hα t.property.1 t.property.2).mp ht
  · intro h
    filter_upwards [h] with t ht
    exact (thetaDiagonal_equality_points hα t.property.1 t.property.2).mpr ht

/-- Exact transfer step; the hypothesis here is the separately proved hyperbolic inequality. -/
theorem thetaMoment_bound_from_hyperbolic {α : ℝ} (hα : 0 < α)
    (μ : ProbabilityMeasure HalfInterval)
    (hH : 2 * Real.cosh (thetaR α) *
      geometricMean (centeredCoshMap (thetaR α)) (thetaPush hα μ) ≤
        hyperbolicNumerator (thetaR α) (thetaPush hα μ)) :
    2 * (gaussian α 0 * gaussian α (1 / 2)) ^ 4 ≤ thetaMomentNumerator hα μ := by
  have hK := thetaNormalization_pos hα μ
  have hnum := thetaMomentNumerator_factorization hα μ
  have hdiag := thetaDiagonal_geometric_factorization hα μ
  have hlower := thetaDiagonal_geometric_lower hα μ
  have hmul := mul_le_mul_of_nonneg_left hH hK.le
  nlinarith [hmul]

/-- Equality is retained at both stages of the transfer, including singular measures. -/
theorem thetaMoment_equality_from_hyperbolic {α : ℝ} (hα : 0 < α)
    (μ : ProbabilityMeasure HalfInterval)
    (hH : 2 * Real.cosh (thetaR α) *
      geometricMean (centeredCoshMap (thetaR α)) (thetaPush hα μ) ≤
        hyperbolicNumerator (thetaR α) (thetaPush hα μ)) :
    thetaMomentNumerator hα μ = 2 * (gaussian α 0 * gaussian α (1 / 2)) ^ 4 ↔
      geometricMean (thetaDiagonalMap hα) μ = (gaussian α 0 * gaussian α (1 / 2)) ^ 4 ∧
      hyperbolicNumerator (thetaR α) (thetaPush hα μ) = 2 * Real.cosh (thetaR α) *
        geometricMean (centeredCoshMap (thetaR α)) (thetaPush hα μ) := by
  have hK := thetaNormalization_pos hα μ
  have hnum := thetaMomentNumerator_factorization hα μ
  have hdiag := thetaDiagonal_geometric_factorization hα μ
  have hlower := thetaDiagonal_geometric_lower hα μ
  have hmul := mul_le_mul_of_nonneg_left hH hK.le
  constructor
  · intro heq
    have hd : geometricMean (thetaDiagonalMap hα) μ =
        (gaussian α 0 * gaussian α (1 / 2)) ^ 4 := by nlinarith [hmul]
    refine ⟨hd, ?_⟩
    apply mul_left_cancel₀ hK.ne'
    calc
      thetaNormalization hα μ * hyperbolicNumerator (thetaR α) (thetaPush hα μ) =
          thetaMomentNumerator hα μ := hnum.symm
      _ = 2 * (gaussian α 0 * gaussian α (1 / 2)) ^ 4 := heq
      _ = 2 * geometricMean (thetaDiagonalMap hα) μ := by rw [hd]
      _ = _ := by rw [hdiag]; ring
  · rintro ⟨hd, heq⟩
    rw [heq] at hnum
    nlinarith only [hnum, hdiag, hd]

end PaperVerification.ColdSpots

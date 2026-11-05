module

public import VolumePolynomials.KernelTestMeasure
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
public import Mathlib.MeasureTheory.VectorMeasure.Integral

@[expose] public section

/-!
# Kernel energy for every finite real signed measure

Integration is the difference of the integrals against the two actual Jordan
parts. The energy is the corresponding double integral of the exponential
kernel, and is proved equal to a squared Hilbert norm. No positive-definiteness
or energy Cauchy–Schwarz assertion is assumed.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace VolumePolynomials

noncomputable def signedRealIntegral (ν : SignedMeasure ℝ) (f : ℝ → ℝ) : ℝ :=
  (∫ x, f x ∂ν.toJordanDecomposition.posPart) -
    ∫ x, f x ∂ν.toJordanDecomposition.negPart

/-- Agreement with Mathlib's signed-measure integral on its full integrable domain. -/
theorem signedRealIntegral_eq_vectorIntegral (ν : SignedMeasure ℝ) (f : ℝ → ℝ)
    (hp : Integrable f ν.toJordanDecomposition.posPart)
    (hn : Integrable f ν.toJordanDecomposition.negPart) :
    signedRealIntegral ν f = ∫ᵛ x, f x ∂<•ν := by
  have hp' : ν.toJordanDecomposition.posPart.toSignedMeasure.Integrable f := by
    simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using hp
  have hn' : ν.toJordanDecomposition.negPart.toSignedMeasure.Integrable f := by
    simpa only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure] using hn
  conv_rhs => rw [← ν.toSignedMeasure_toJordanDecomposition]
  rw [JordanDecomposition.toSignedMeasure, VectorMeasure.integral_sub_vectorMeasure hp' hn',
    VectorMeasure.integral_toSignedMeasure, VectorMeasure.integral_toSignedMeasure]
  rfl

noncomputable def cornerSignedMean (ν : SignedMeasure ℝ) : Lp ℝ 2 (volume : Measure ℝ) :=
  cornerMean ν.toJordanDecomposition.posPart - cornerMean ν.toJordanDecomposition.negPart

/-- The genuine double kernel integral against the signed measure. -/
noncomputable def cornerSignedEnergy (ν : SignedMeasure ℝ) : ℝ :=
  signedRealIntegral ν (fun x => signedRealIntegral ν (cornerKernel x))

theorem signedRealIntegral_const_one (ν : SignedMeasure ℝ) :
    signedRealIntegral ν (fun _ => 1) = ν univ := by
  rw [ν.apply_eq_posPart_real_sub_negPart_real MeasurableSet.univ]
  simp only [signedRealIntegral, integral_const, smul_eq_mul, mul_one]

theorem inner_cornerFeature_signedMean (ν : SignedMeasure ℝ) (x : ℝ) :
    ⟪cornerFeature x, cornerSignedMean ν⟫_ℝ = signedRealIntegral ν (cornerKernel x) := by
  simp only [cornerSignedMean, inner_sub_right, inner_cornerFeature_mean, signedRealIntegral]

theorem signedRealIntegral_inner_cornerFeature (ν : SignedMeasure ℝ)
    (u : Lp ℝ 2 (volume : Measure ℝ)) :
    signedRealIntegral ν (fun x => ⟪cornerFeature x, u⟫_ℝ) =
      ⟪cornerSignedMean ν, u⟫_ℝ := by
  have hf : (fun x => ⟪cornerFeature x, u⟫_ℝ) =
      (fun x => ⟪u, cornerFeature x⟫_ℝ) :=
    funext (fun x => (real_inner_comm (cornerFeature x) u).symm)
  rw [hf, signedRealIntegral, integral_inner (integrable_cornerFeature _),
    integral_inner (integrable_cornerFeature _)]
  change ⟪u, cornerMean ν.toJordanDecomposition.posPart⟫_ℝ -
      ⟪u, cornerMean ν.toJordanDecomposition.negPart⟫_ℝ =
    ⟪cornerMean ν.toJordanDecomposition.posPart - cornerMean ν.toJordanDecomposition.negPart, u⟫_ℝ
  rw [inner_sub_left, real_inner_comm u (cornerMean ν.toJordanDecomposition.posPart),
    real_inner_comm u (cornerMean ν.toJordanDecomposition.negPart)]

theorem cornerSignedEnergy_eq_norm_sq (ν : SignedMeasure ℝ) :
    cornerSignedEnergy ν = ‖cornerSignedMean ν‖ ^ 2 := by
  unfold cornerSignedEnergy
  simp_rw [← inner_cornerFeature_signedMean]
  rw [signedRealIntegral_inner_cornerFeature, real_inner_self_eq_norm_sq]

/-- The energy agrees with the iterated signed-measure integral in the paper. -/
theorem cornerSignedEnergy_eq_double_vectorIntegral (ν : SignedMeasure ℝ) :
    cornerSignedEnergy ν = ∫ᵛ x, (∫ᵛ y, cornerKernel x y ∂<•ν) ∂<•ν := by
  have hint (μ : Measure ℝ) [IsFiniteMeasure μ] :
      Integrable (fun x => signedRealIntegral ν (cornerKernel x)) μ := by
    simp_rw [← inner_cornerFeature_signedMean]
    exact (integrable_cornerFeature μ).inner_const (cornerSignedMean ν)
  rw [cornerSignedEnergy,
    signedRealIntegral_eq_vectorIntegral ν _ (hint _) (hint _)]
  apply VectorMeasure.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  exact signedRealIntegral_eq_vectorIntegral ν (cornerKernel x)
    (integrable_cornerKernel _ x) (integrable_cornerKernel _ x)

theorem cornerSignedEnergy_nonneg (ν : SignedMeasure ℝ) : 0 ≤ cornerSignedEnergy ν := by
  rw [cornerSignedEnergy_eq_norm_sq]
  exact sq_nonneg _

theorem inner_cornerSignedMean_test {R : ℝ} (hR : 0 ≤ R) (ν : SignedMeasure ℝ) :
    ⟪cornerSignedMean ν, cornerMean (cornerTestMeasure R)⟫_ℝ =
      signedRealIntegral ν (cornerTestPotential R) := by
  rw [← signedRealIntegral_inner_cornerFeature]
  simp_rw [inner_cornerFeature_mean, integral_cornerTestMeasure hR]

theorem cornerTestPotential_error_nonneg {R : ℝ} (hR : 0 ≤ R) (x : ℝ) :
    0 ≤ 1 - cornerTestPotential R x := sub_nonneg.mpr (cornerTestPotential_le_one hR x)

theorem cornerTestPotential_error_le {R : ℝ} (hR : 0 ≤ R) (x : ℝ) :
    1 - cornerTestPotential R x ≤ Real.exp (-R / 2) * Real.exp (|x| / 2) := by
  rw [← Real.exp_add]
  have hexponent : -R / 2 + |x| / 2 = (|x| - R) / 2 := by ring
  rw [hexponent, cornerTestPotential_eq hR]
  split_ifs with hx
  · simpa using (Real.exp_pos ((|x| - R) / 2)).le
  · have hnonneg : 0 ≤ (|x| - R) / 2 := by linarith [le_of_not_ge hx]
    have hle : 1 ≤ Real.exp ((|x| - R) / 2) := Real.one_le_exp_iff.mpr hnonneg
    linarith [Real.exp_pos (-(|x| - R) / 2)]

theorem integrable_cornerTestPotential_error {R : ℝ} (hR : 0 ≤ R)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (fun x => 1 - cornerTestPotential R x) μ :=
  (integrable_const 1).sub (integrable_cornerTestPotential hR μ)

theorem signedRealIntegral_test_error {R : ℝ} (hR : 0 ≤ R) (ν : SignedMeasure ℝ) :
    ν univ - ⟪cornerSignedMean ν, cornerMean (cornerTestMeasure R)⟫_ℝ =
      signedRealIntegral ν (fun x => 1 - cornerTestPotential R x) := by
  rw [inner_cornerSignedMean_test hR, ← signedRealIntegral_const_one ν]
  simp only [signedRealIntegral,
    integral_sub (integrable_const 1) (integrable_cornerTestPotential hR _)]
  ring

/-- The signed testing error is controlled by the actual exponential moment of
the total variation. Integrability is stated explicitly to avoid Bochner's
zero value on nonintegrable functions. -/
theorem signed_test_error_bound {R : ℝ} (hR : 0 ≤ R) (ν : SignedMeasure ℝ)
    (hInt : Integrable (fun x : ℝ => Real.exp (|x| / 2)) ν.totalVariation)
    (hMoment : (∫ x : ℝ, Real.exp (|x| / 2) ∂ν.totalVariation) ≤ 4) :
    |ν univ - ⟪cornerSignedMean ν, cornerMean (cornerTestMeasure R)⟫_ℝ| ≤
      4 * Real.exp (-R / 2) := by
  rw [signedRealIntegral_test_error hR]
  have hp : 0 ≤ ∫ x, (1 - cornerTestPotential R x) ∂ν.toJordanDecomposition.posPart :=
    integral_nonneg (cornerTestPotential_error_nonneg hR)
  have hn : 0 ≤ ∫ x, (1 - cornerTestPotential R x) ∂ν.toJordanDecomposition.negPart :=
    integral_nonneg (cornerTestPotential_error_nonneg hR)
  calc
    |signedRealIntegral ν (fun x => 1 - cornerTestPotential R x)|
        ≤ (∫ x, (1 - cornerTestPotential R x) ∂ν.toJordanDecomposition.posPart) +
          ∫ x, (1 - cornerTestPotential R x) ∂ν.toJordanDecomposition.negPart := by
      unfold signedRealIntegral
      apply abs_le.mpr
      constructor <;> linarith
    _ = ∫ x, (1 - cornerTestPotential R x) ∂ν.totalVariation := by
      rw [SignedMeasure.totalVariation,
        integral_add_measure (integrable_cornerTestPotential_error hR _)
          (integrable_cornerTestPotential_error hR _)]
    _ ≤ Real.exp (-R / 2) * ∫ x : ℝ, Real.exp (|x| / 2) ∂ν.totalVariation := by
      rw [← integral_const_mul]
      apply integral_mono (integrable_cornerTestPotential_error hR _)
        (hInt.const_mul _)
      exact cornerTestPotential_error_le hR
    _ ≤ 4 * Real.exp (-R / 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hMoment (Real.exp_pos (-R / 2)).le]

/-- The complete testing estimate in the first line of the proof of Lemma5.1. -/
theorem signed_mass_test_bound {R : ℝ} (hR : 0 ≤ R) (ν : SignedMeasure ℝ)
    (hInt : Integrable (fun x : ℝ => Real.exp (|x| / 2)) ν.totalVariation)
    (hMoment : (∫ x : ℝ, Real.exp (|x| / 2) ∂ν.totalVariation) ≤ 4) :
    |ν univ| ≤ ‖cornerSignedMean ν‖ * ‖cornerMean (cornerTestMeasure R)‖ +
      4 * Real.exp (-R / 2) := by
  have herror := signed_test_error_bound hR ν hInt hMoment
  have hCS := abs_real_inner_le_norm (cornerSignedMean ν) (cornerMean (cornerTestMeasure R))
  have htriangle := abs_add_le
    ⟪cornerSignedMean ν, cornerMean (cornerTestMeasure R)⟫_ℝ
    (ν univ - ⟪cornerSignedMean ν, cornerMean (cornerTestMeasure R)⟫_ℝ)
  have hsum : ⟪cornerSignedMean ν, cornerMean (cornerTestMeasure R)⟫_ℝ +
      (ν univ - ⟪cornerSignedMean ν, cornerMean (cornerTestMeasure R)⟫_ℝ) = ν univ := by
    ring
  rw [hsum] at htriangle
  linarith

end VolumePolynomials

module

public import wishart.verified.finite_order_stein

/-!
# Finite-order Stein identities for the actual Gaussian Gram laws

Only one continuous derivative is needed here. Polynomial bounds are imposed
on the positive semidefinite cone, which contains the support of the Gram law
and every translated input used in the proof. The identity includes singular
natural degrees and degree zero.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti.Probability Matrix Set
open WishartVerification
open scoped RealInnerProductSpace Matrix.Norms.L2Operator

namespace Wishart.FiniteOrder

section Convolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A linear Stein identity with growth controlled on a set closed under the
translations actually used by the measure. -/
def LinearSteinIdentityOn (s : Set E) (μ : Measure E)
    (B : E →L[ℝ] E) (c : E →L[ℝ] ℝ) (a : ℝ) : Prop :=
  ∀ (g : E → ℝ), C1PolynomialOn s g → ∀ T ∈ s,
    (∫ X, fderiv ℝ g (X + T) (B X) ∂μ) =
      ∫ X, (c X - a) * g (X + T) ∂μ

theorem continuous_linearSteinDerivative_c1 (B : E →L[ℝ] E) (T : E)
    {s : Set E} {g : E → ℝ} (hg : C1PolynomialOn s g) :
    Continuous (fun X => fderiv ℝ g (X + T) (B X)) := by
  exact ((hg.regular.continuous_fderiv (by norm_num)).comp
    (continuous_id.add continuous_const)).clm_apply B.continuous

theorem continuous_linearSteinScore_c1 (c : E →L[ℝ] ℝ) (a : ℝ) (T : E)
    {s : Set E} {g : E → ℝ} (hg : C1PolynomialOn s g) :
    Continuous (fun X => (c X - a) * g (X + T)) := by
  exact (c.continuous.sub continuous_const).mul
    (hg.regular.continuous.comp (continuous_id.add continuous_const))

theorem linearSteinIdentityOn_dirac_zero (s : Set E)
    (B : E →L[ℝ] E) (c : E →L[ℝ] ℝ) :
    LinearSteinIdentityOn s (Measure.dirac 0) B c 0 := by
  intro g hg T hT
  simp only [integral_dirac, map_zero, zero_add, sub_zero, zero_mul]

/-- Independent addition preserves the support-restricted identity. The two
integrability arguments use only the value and first derivative bounds. -/
theorem linearSteinIdentityOn_conv {s : Set E}
    (hadd : ∀ ⦃X Y : E⦄, X ∈ s → Y ∈ s → X + Y ∈ s)
    {μ ν : Measure E} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : HasAllFiniteMoments (fun X : E => ‖X‖) μ)
    (hν : HasAllFiniteMoments (fun X : E => ‖X‖) ν)
    (hμs : ∀ᵐ X ∂μ, X ∈ s) (hνs : ∀ᵐ Y ∂ν, Y ∈ s)
    (B : E →L[ℝ] E) (c : E →L[ℝ] ℝ) (a b : ℝ)
    (hμstein : LinearSteinIdentityOn s μ B c a)
    (hνstein : LinearSteinIdentityOn s ν B c b) :
    LinearSteinIdentityOn s (μ ∗ ν) B c (a + b) := by
  intro g hg T hT
  let μp := μ.prod ν
  let V : E × E → E := fun z => z.1 + z.2 + T
  let L₁ : E × E → ℝ := fun z => fderiv ℝ g (V z) (B z.1)
  let L₂ : E × E → ℝ := fun z => fderiv ℝ g (V z) (B z.2)
  let R₁ : E × E → ℝ := fun z => (c z.1 - a) * g (V z)
  let R₂ : E × E → ℝ := fun z => (c z.2 - b) * g (V z)
  have hp : HasAllFiniteMoments (fun z : E × E => ‖z‖) μp :=
    allFiniteNormMoments_prod hμ hν
  have hps : ∀ᵐ z ∂μp, z ∈ s ×ˢ s := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hμs,
      Measure.quasiMeasurePreserving_snd.ae hνs] with z hz₁ hz₂
    exact ⟨hz₁, hz₂⟩
  have hfst : PolynomialBoundOn (s ×ˢ s) (fun z : E × E => z.1) :=
    PolynomialBoundOn.of_temperate (ContinuousLinearMap.fst ℝ E E).hasTemperateGrowth
  have hsnd : PolynomialBoundOn (s ×ˢ s) (fun z : E × E => z.2) :=
    PolynomialBoundOn.of_temperate (ContinuousLinearMap.snd ℝ E E).hasTemperateGrowth
  have hV : PolynomialBoundOn (s ×ˢ s) V :=
    (hfst.add hsnd).add (PolynomialBoundOn.const _ T)
  have hVs : MapsTo V (s ×ˢ s) s := fun _ hz => hadd (hadd hz.1 hz.2) hT
  have hd := hg.derivative.comp hV hVs
  have hgf := hg.value.comp hV hVs
  have hB₁ : PolynomialBoundOn (s ×ˢ s) (fun z : E × E => B z.1) :=
    PolynomialBoundOn.of_temperate
      (B.hasTemperateGrowth.comp (ContinuousLinearMap.fst ℝ E E).hasTemperateGrowth)
  have hB₂ : PolynomialBoundOn (s ×ˢ s) (fun z : E × E => B z.2) :=
    PolynomialBoundOn.of_temperate
      (B.hasTemperateGrowth.comp (ContinuousLinearMap.snd ℝ E E).hasTemperateGrowth)
  have hL₁c : Continuous L₁ :=
    ((hg.regular.continuous_fderiv (by norm_num)).comp
      ((continuous_fst.add continuous_snd).add continuous_const)).clm_apply
        (B.continuous.comp continuous_fst)
  have hL₂c : Continuous L₂ :=
    ((hg.regular.continuous_fderiv (by norm_num)).comp
      ((continuous_fst.add continuous_snd).add continuous_const)).clm_apply
        (B.continuous.comp continuous_snd)
  have hR₁c : Continuous R₁ :=
    ((c.continuous.comp continuous_fst).sub continuous_const).mul
      (hg.regular.continuous.comp ((continuous_fst.add continuous_snd).add continuous_const))
  have hR₂c : Continuous R₂ :=
    ((c.continuous.comp continuous_snd).sub continuous_const).mul
      (hg.regular.continuous.comp ((continuous_fst.add continuous_snd).add continuous_const))
  have hL₁ : Integrable L₁ μp :=
    (hd.clm_apply hB₁).integrable hp hL₁c.aestronglyMeasurable hps
  have hL₂ : Integrable L₂ μp :=
    (hd.clm_apply hB₂).integrable hp hL₂c.aestronglyMeasurable hps
  have hR₁ : Integrable R₁ μp := by
    apply PolynomialBoundOn.integrable hp _ hR₁c.aestronglyMeasurable hps
    exact ((PolynomialBoundOn.of_temperate
      (c.hasTemperateGrowth.comp (ContinuousLinearMap.fst ℝ E E).hasTemperateGrowth)).sub
        (PolynomialBoundOn.const _ a)).mul hgf
  have hR₂ : Integrable R₂ μp := by
    apply PolynomialBoundOn.integrable hp _ hR₂c.aestronglyMeasurable hps
    exact ((PolynomialBoundOn.of_temperate
      (c.hasTemperateGrowth.comp (ContinuousLinearMap.snd ℝ E E).hasTemperateGrowth)).sub
        (PolynomialBoundOn.const _ b)).mul hgf
  have heq₁ : (∫ z, L₁ z ∂μp) = ∫ z, R₁ z ∂μp := by
    rw [integral_prod_symm _ hL₁, integral_prod_symm _ hR₁]
    apply integral_congr_ae
    filter_upwards [hνs] with Y hY
    simpa only [L₁, R₁, V, add_assoc] using hμstein g hg (Y + T) (hadd hY hT)
  have heq₂ : (∫ z, L₂ z ∂μp) = ∫ z, R₂ z ∂μp := by
    rw [integral_prod _ hL₂, integral_prod _ hR₂]
    apply integral_congr_ae
    filter_upwards [hμs] with X hX
    simpa only [L₂, R₂, V, add_assoc, add_comm, add_left_comm] using
      hνstein g hg (X + T) (hadd hX hT)
  have hleft := continuous_linearSteinDerivative_c1 B T hg
  have hright := continuous_linearSteinScore_c1 c (a + b) T hg
  rw [Measure.conv,
    integral_map (by fun_prop) hleft.aestronglyMeasurable,
    integral_map (by fun_prop) hright.aestronglyMeasurable]
  calc
    (∫ z : E × E, fderiv ℝ g (z.1 + z.2 + T) (B (z.1 + z.2)) ∂μ.prod ν) =
        ∫ z, L₁ z + L₂ z ∂μp := by
      apply integral_congr_ae
      filter_upwards with z
      simp only [map_add, L₁, L₂, V]
    _ = (∫ z, L₁ z ∂μp) + ∫ z, L₂ z ∂μp := integral_add hL₁ hL₂
    _ = (∫ z, R₁ z ∂μp) + ∫ z, R₂ z ∂μp := by rw [heq₁, heq₂]
    _ = ∫ z, R₁ z + R₂ z ∂μp := (integral_add hR₁ hR₂).symm
    _ = ∫ z : E × E, (c (z.1 + z.2) - (a + b)) * g (z.1 + z.2 + T) ∂μ.prod ν := by
      apply integral_congr_ae
      filter_upwards with z
      simp only [R₁, R₂, V, map_add]
      ring

end Convolution

section Gram

variable {p : ℕ}

/-- The rank-one Gaussian identity needs one derivative, with growth bounds
only on the cone visited by the translated rank-one matrices. -/
theorem gaussian_rankOne_stein_c1 {C : Matrix (Fin p) (Fin p) ℝ} (hC : C.PosDef)
    {g : SymmetricMatrix p → ℝ} (hg : C1PolynomialOn (psdCone p) g)
    (T : SymmetricMatrix p) (hT : T ∈ psdCone p)
    (u v : EuclideanSpace ℝ (Fin p)) :
    (∫ z, ⟪u, z⟫ * fderiv ℝ g (T + rankOneSymmetric z)
      (symmetricRankDirection v z) ∂multivariateGaussian 0 C) =
    ∫ z, (⟪v, C⁻¹.toEuclideanLin z⟫ * ⟪u, z⟫ - ⟪u, v⟫) *
      g (T + rankOneSymmetric z) ∂multivariateGaussian 0 C := by
  let V : EuclideanSpace ℝ (Fin p) → SymmetricMatrix p := fun z => T + rankOneSymmetric z
  let f : EuclideanSpace ℝ (Fin p) → ℝ := fun z => ⟪u, z⟫ * g (V z)
  let L : EuclideanSpace ℝ (Fin p) → ℝ := fun z =>
    ⟪u, z⟫ * fderiv ℝ g (V z) (symmetricRankDirection v z)
  let G : EuclideanSpace ℝ (Fin p) → ℝ := fun z =>
    (⟪v, C⁻¹.toEuclideanLin z⟫ * ⟪u, z⟫) * g (V z)
  have hV : C1PolynomialOn univ V :=
    C1PolynomialOn.of_temperate
      ((Function.HasTemperateGrowth.const T).add hasTemperateGrowth_rankOneSymmetric)
  have hVs : MapsTo V univ (psdCone p) := fun z _ => hT.add (rankOneSymmetric_posSemidef z)
  have hgf : C1PolynomialOn univ (fun z => g (V z)) := hg.comp hV hVs
  have hinner : C1PolynomialOn univ (fun z : EuclideanSpace ℝ (Fin p) => ⟪u, z⟫) :=
    C1PolynomialOn.of_temperate (innerSL ℝ u).hasTemperateGrowth
  have hf : C1PolynomialOn univ f := hinner.mul hgf
  have hL : PolynomialBoundOn univ L :=
    hinner.value.mul ((hg.derivative.comp hV.value hVs).clm_apply
      (PolynomialBoundOn.of_temperate (symmetricRankDirection v).hasTemperateGrowth))
  have hscore : (fun z : EuclideanSpace ℝ (Fin p) =>
      ⟪v, C⁻¹.toEuclideanLin z⟫ * ⟪u, z⟫).HasTemperateGrowth := by
    simpa only [Function.comp_def, Pi.mul_def, innerSL_apply_apply,
      LinearMap.coe_toContinuousLinearMap'] using
      ((innerSL ℝ v).hasTemperateGrowth.comp
        C⁻¹.toEuclideanLin.toContinuousLinearMap.hasTemperateGrowth).mul
          (innerSL ℝ u).hasTemperateGrowth
  have hG : PolynomialBoundOn univ G :=
    (PolynomialBoundOn.of_temperate hscore).mul hgf.value
  have hμ := allFiniteMoments_gaussian_norm (μ := multivariateGaussian 0 C)
  have hsupport : ∀ᵐ z ∂multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) C,
      z ∈ (univ : Set (EuclideanSpace ℝ (Fin p))) :=
    Filter.Eventually.of_forall (mem_univ ·)
  have hLc : Continuous L := hinner.regular.continuous.mul
    (((hg.regular.continuous_fderiv (by norm_num)).comp hV.regular.continuous).clm_apply
      (symmetricRankDirection v).continuous)
  have hLi := hL.integrable hμ hLc.aestronglyMeasurable hsupport
  have hGi := hG.integrable hμ
    (hscore.1.continuous.mul hgf.regular.continuous).aestronglyMeasurable hsupport
  have hfi := hgf.value.integrable hμ hgf.regular.continuous.aestronglyMeasurable hsupport
  have hd (z : EuclideanSpace ℝ (Fin p)) :
      fderiv ℝ f z v = ⟪u, v⟫ * g (V z) + L z := by
    have hderiv := ((innerSL ℝ u).hasFDerivAt.mul
      ((hg.regular.differentiable (by norm_num) (V z)).hasFDerivAt.comp z
        ((hasFDerivAt_rankOneSymmetric z).const_add T))).fderiv
    have heval := congrArg (fun A : EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ => A v) hderiv
    simpa only [f, V, L, Function.comp_def, Pi.mul_def, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply, smul_eq_mul, symmetricRankDirection_comm,
      mul_comm, add_comm] using heval
  have hs := gaussian_stein_c1 hC hf v
  simp_rw [hd] at hs
  have hGi' : (∫ z, ⟪v, C⁻¹.toEuclideanLin z⟫ * f z ∂multivariateGaussian 0 C) =
      ∫ z, G z ∂multivariateGaussian 0 C := by
    apply integral_congr_ae
    filter_upwards with z
    dsimp only [f, G]
    ring
  rw [hGi', integral_add (hfi.const_mul ⟪u, v⟫) hLi, integral_const_mul] at hs
  change (∫ z, L z ∂multivariateGaussian 0 C) = _
  have heq : (fun z => (⟪v, C⁻¹.toEuclideanLin z⟫ * ⟪u, z⟫ - ⟪u, v⟫) *
      g (T + rankOneSymmetric z)) = (fun z => G z - ⟪u, v⟫ * g (V z)) := by
    funext z
    dsimp only [G, V]
    ring
  rw [heq, integral_sub hGi (hfi.const_mul ⟪u, v⟫), integral_const_mul]
  linarith

theorem linearSteinIdentityOn_gram_one {C : Matrix (Fin p) (Fin p) ℝ}
    (hC : C.PosDef) (u v : EuclideanSpace ℝ (Fin p)) :
    LinearSteinIdentityOn (psdCone p) (wishartGramMeasure 1 C)
      (gramSteinDirection u v) (gramSteinScore C u v) ⟪u, v⟫ := by
  intro g hg T hT
  have hleft := continuous_linearSteinDerivative_c1 (gramSteinDirection u v) T hg
  have hright := continuous_linearSteinScore_c1 (gramSteinScore C u v) ⟪u, v⟫ T hg
  rw [← map_rankOneSymmetric_gaussian C,
    integral_map hasTemperateGrowth_rankOneSymmetric.1.continuous.measurable.aemeasurable
      hleft.aestronglyMeasurable,
    integral_map hasTemperateGrowth_rankOneSymmetric.1.continuous.measurable.aemeasurable
      hright.aestronglyMeasurable]
  simpa only [gramSteinDirection_rankOne, gramSteinScore_rankOne hC,
    map_smul, smul_eq_mul, add_comm] using gaussian_rankOne_stein_c1 hC hg T hT u v

/-- Natural Gram degrees are obtained by adding independent rows. Neither a
density on the ambient cone nor nonsingularity of the Gram matrix is assumed. -/
theorem linearSteinIdentityOn_gram (n : ℕ) {C : Matrix (Fin p) (Fin p) ℝ}
    (hC : C.PosDef) (u v : EuclideanSpace ℝ (Fin p)) :
    LinearSteinIdentityOn (psdCone p) (wishartGramMeasure n C)
      (gramSteinDirection u v) (gramSteinScore C u v) ((n : ℝ) * ⟪u, v⟫) := by
  induction n with
  | zero =>
      simpa only [wishartGramMeasure_zero, Nat.cast_zero, zero_mul] using
        linearSteinIdentityOn_dirac_zero (psdCone p)
          (gramSteinDirection u v) (gramSteinScore C u v)
  | succ n ih =>
      have h := linearSteinIdentityOn_conv
        (s := psdCone p) (by intro X Y hX hY; exact hX.add hY)
        (allFiniteMoments_gram_norm n C) (allFiniteMoments_gram_norm 1 C)
        (ae_posSemidef_wishartGramMeasure n C) (ae_posSemidef_wishartGramMeasure 1 C)
        (gramSteinDirection u v) (gramSteinScore C u v)
        ((n : ℝ) * ⟪u, v⟫) ⟪u, v⟫ ih (linearSteinIdentityOn_gram_one hC u v)
      rw [wishartGramMeasure_conv_wishartGramMeasure] at h
      have ha : ((n + 1 : ℕ) : ℝ) * ⟪u, v⟫ = (n : ℝ) * ⟪u, v⟫ + ⟪u, v⟫ := by
        push_cast
        ring
      simpa only [Nat.succ_eq_add_one, ha] using h

/-- The actual natural-degree Gram Stein identity for C¹ tests whose value
and first derivative grow polynomially only on the positive semidefinite cone. -/
theorem gram_stein_translate_c1 (n : ℕ) {C : Matrix (Fin p) (Fin p) ℝ}
    (hC : C.PosDef) {g : SymmetricMatrix p → ℝ} (hg : C1PolynomialOn (psdCone p) g)
    (T : SymmetricMatrix p) (hT : T ∈ psdCone p) (u v : EuclideanSpace ℝ (Fin p)) :
    (∫ W, fderiv ℝ g (W + T)
      (symmetricRankDirection v (symmetricMatrixAction W u)) ∂wishartGramMeasure n C) =
      ∫ W, (⟪u, symmetricMatrixAction W (C⁻¹.toEuclideanLin v)⟫ -
        (n : ℝ) * ⟪u, v⟫) * g (W + T) ∂wishartGramMeasure n C :=
  linearSteinIdentityOn_gram n hC u v g hg T hT

end Gram

end Wishart.FiniteOrder

end

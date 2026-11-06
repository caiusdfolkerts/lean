module

public import wishart.verified.real_remainder06

/- Generated ordinary proof stage. See audit/staged_real_remainder/RealRemainder07/manifest.json. -/

@[expose] public section

section CanonicalSource60
/- Source: Wishart/GaussianAnderson.lean -/



/-!
# Anderson comparison along a complete translating ray

Prékopa–Leindler applied to two opposite translates gives comparison between
every two nonnegative displacements. The Gaussian may be the image of any
rectangular linear map, including the zero map, and the displacement need not
belong to its range. Thus the proof also handles singular covariance directly.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Wishart

variable {ι : Type*} [Fintype ι]

def gaussianPiDensity (x : ι → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))

@[fun_prop] theorem measurable_gaussianPiDensity :
    Measurable (gaussianPiDensity (ι := ι)) :=
  (TauCeti.Probability.measurable_prod_gaussianPDFReal ι).ennreal_ofReal

theorem gaussianPiDensity_log_concave {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (x y : ι → ℝ) :
    gaussianPiDensity x ^ a * gaussianPiDensity y ^ (1 - a) ≤
      gaussianPiDensity (a • x + (1 - a) • y) := by
  classical
  have hc : 0 < (2 * Real.pi) ^ (-(Fintype.card ι : ℝ) / 2) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hquadratic :
      (∑ i, (a * x i + (1 - a) * y i) ^ 2) ≤
        a * (∑ i, x i ^ 2) + (1 - a) * (∑ i, y i ^ 2) := by
    calc
      _ ≤ ∑ i, (a * x i ^ 2 + (1 - a) * y i ^ 2) := by
        apply Finset.sum_le_sum
        intro i _
        have h := mul_nonneg (mul_nonneg ha (sub_nonneg.mpr ha1))
          (sq_nonneg (x i - y i))
        nlinarith
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hreal :
      (∏ i, gaussianPDFReal 0 1 (x i)) ^ a *
          (∏ i, gaussianPDFReal 0 1 (y i)) ^ (1 - a) ≤
        ∏ i, gaussianPDFReal 0 1 ((a • x + (1 - a) • y) i) := by
    rw [TauCeti.Probability.prod_gaussianPDFReal_zero_one,
      TauCeti.Probability.prod_gaussianPDFReal_zero_one,
      TauCeti.Probability.prod_gaussianPDFReal_zero_one]
    rw [Real.mul_rpow hc.le (Real.exp_pos _).le,
      Real.mul_rpow hc.le (Real.exp_pos _).le,
      ← Real.exp_mul, ← Real.exp_mul]
    rw [show ((2 * Real.pi) ^ (-(Fintype.card ι : ℝ) / 2)) ^ a *
          Real.exp (-(∑ i, x i ^ 2) / 2 * a) *
          (((2 * Real.pi) ^ (-(Fintype.card ι : ℝ) / 2)) ^ (1 - a) *
          Real.exp (-(∑ i, y i ^ 2) / 2 * (1 - a))) =
        (((2 * Real.pi) ^ (-(Fintype.card ι : ℝ) / 2)) ^ a *
          ((2 * Real.pi) ^ (-(Fintype.card ι : ℝ) / 2)) ^ (1 - a)) *
          (Real.exp (-(∑ i, x i ^ 2) / 2 * a) *
          Real.exp (-(∑ i, y i ^ 2) / 2 * (1 - a))) by ring,
      ← Real.rpow_add hc, show a + (1 - a) = 1 by ring, Real.rpow_one,
      ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ hc.le
    apply Real.exp_le_exp_of_le
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  unfold gaussianPiDensity
  rw [ENNReal.ofReal_rpow_of_pos (TauCeti.Probability.prod_gaussianPDFReal_pos ι x),
    ENNReal.ofReal_rpow_of_pos (TauCeti.Probability.prod_gaussianPDFReal_pos ι y),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg
      (TauCeti.Probability.prod_gaussianPDFReal_pos ι x).le _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem piGaussian_eq_volume_withDensity :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      (volume : Measure (ι → ℝ)).withDensity gaussianPiDensity := by
  change (Measure.pi (fun _ : ι => gaussianReal 0 1)) =
    (volume : Measure (ι → ℝ)).withDensity
      (fun x => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i)))
  simpa only [volume_pi] using
    TauCeti.Probability.pi_gaussianReal_eq_withDensity ι

theorem piGaussian_geometric_measure_le
    {A B C : Set (ι → ℝ)} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : MeasurableSet C) {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hmean : ∀ x ∈ A, ∀ y ∈ B, a • x + (1 - a) • y ∈ C) :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)) A ^ a *
        (Measure.pi (fun _ : ι => gaussianReal 0 1)) B ^ (1 - a) ≤
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) C := by
  have hsets (S : Set (ι → ℝ)) (hS : MeasurableSet S) :
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) S =
        ∫⁻ x, S.indicator gaussianPiDensity x := by
    rw [piGaussian_eq_volume_withDensity, withDensity_apply _ hS,
      ← lintegral_indicator hS]
  rw [hsets A hA, hsets B hB, hsets C hC]
  apply PrekopaLeindler.prekopaLeindler
    (measurable_gaussianPiDensity.indicator hA)
    (measurable_gaussianPiDensity.indicator hB)
    (measurable_gaussianPiDensity.indicator hC) ha ha1
  intro x y
  by_cases hx : x ∈ A
  · by_cases hy : y ∈ B
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy,
        Set.indicator_of_mem (hmean x hx y hy)]
      exact gaussianPiDensity_log_concave ha.le ha1.le x y
    · rw [Set.indicator_of_notMem hy, ENNReal.zero_rpow_of_pos (sub_pos.mpr ha1), mul_zero]
      exact bot_le
  · rw [Set.indicator_of_notMem hx, ENNReal.zero_rpow_of_pos ha, zero_mul]
    exact bot_le

theorem measurePreserving_neg_piGaussian :
    MeasurePreserving (fun x : ι → ℝ => -x)
      (Measure.pi (fun _ : ι => gaussianReal 0 1))
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  change MeasurePreserving (fun x : ι → ℝ => fun i => -(x i)) _ _
  apply measurePreserving_pi (fun _ : ι => gaussianReal 0 1)
    (fun _ : ι => gaussianReal 0 1) (f := fun _ (x : ℝ) => -x)
  intro i
  exact ⟨measurable_neg, by simpa only [neg_zero] using
    (gaussianReal_map_neg (μ := 0) (v := 1))⟩

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- Gaussian mass of a convex symmetric set decreases along every translating
ray, for arbitrary rectangular Gaussian images and arbitrary displacements. -/
theorem gaussian_anderson_ray (L : (ι → ℝ) →L[ℝ] V) (v : V)
    {C : Set V} (hC : MeasurableSet C) (hconvex : Convex ℝ C)
    (hsymmetric : ∀ x ∈ C, -x ∈ C) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)) {x | L x + t • v ∈ C} ≤
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) {x | L x + s • v ∈ C} := by
  classical
  rcases hst.eq_or_lt with rfl | hst
  · exact le_rfl
  have ht : 0 < t := lt_of_le_of_lt hs hst
  let a : ℝ := (t + s) / (2 * t)
  have ha : 0 < a := div_pos (by linarith) (by positivity)
  have ha1 : a < 1 := (div_lt_one (by positivity : 0 < 2 * t)).mpr (by linarith)
  have hacoef : a * t - (1 - a) * t = s := by
    have h := div_mul_cancel₀ (t + s) (ne_of_gt (by positivity : 0 < 2 * t))
    change a * (2 * t) = t + s at h
    nlinarith
  let A : Set (ι → ℝ) := {x | L x + t • v ∈ C}
  let B : Set (ι → ℝ) := {x | L x - t • v ∈ C}
  let K : Set (ι → ℝ) := {x | L x + s • v ∈ C}
  have hA : MeasurableSet A := hC.preimage (by fun_prop)
  have hB : MeasurableSet B := hC.preimage (by fun_prop)
  have hK : MeasurableSet K := hC.preimage (by fun_prop)
  have hsymm : ∀ x : V, -x ∈ C ↔ x ∈ C := by
    intro x
    exact ⟨fun hx => by simpa only [neg_neg] using hsymmetric (-x) hx, hsymmetric x⟩
  have hBA : B = (fun x : ι → ℝ => -x) ⁻¹' A := by
    ext x
    change L x - t • v ∈ C ↔ L (-x) + t • v ∈ C
    rw [map_neg, show -L x + t • v = -(L x - t • v) by abel]
    exact (hsymm _).symm
  have hmeasure : (Measure.pi (fun _ : ι => gaussianReal 0 1)) B =
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) A := by
    rw [hBA, ← Measure.map_apply (measurePreserving_neg_piGaussian.measurable) hA,
      measurePreserving_neg_piGaussian.map_eq]
  have hmean : ∀ x ∈ A, ∀ y ∈ B, a • x + (1 - a) • y ∈ K := by
    intro x hx y hy
    change L (a • x + (1 - a) • y) + s • v ∈ C
    have heq : L (a • x + (1 - a) • y) + s • v =
        a • (L x + t • v) + (1 - a) • (L y - t • v) := by
      rw [map_add, map_smul, map_smul, ← hacoef]
      simp only [smul_add, smul_sub, smul_smul, sub_smul]
      abel
    rw [heq]
    exact hconvex hx hy ha.le (sub_nonneg.mpr ha1.le) (by ring)
  have h := piGaussian_geometric_measure_le hA hB hK ha ha1 hmean
  rw [hmeasure, ← ENNReal.rpow_add_of_nonneg a (1 - a) ha.le
    (sub_nonneg.mpr ha1.le), show a + (1 - a) = 1 by ring, ENNReal.rpow_one] at h
  exact h

/-- The distribution-function form of Anderson. Convex sublevel sets are the
exact geometric condition needed, so this also applies to even quasiconvex
tests, without differentiability or strict convexity assumptions. -/
theorem cdf_gaussian_even_quasiconvex_shift_antitone
    (L : (ι → ℝ) →L[ℝ] V) (v : V) {g : V → ℝ} (hgm : Measurable g)
    (heven : ∀ x, g (-x) = g x)
    (hconvex : ∀ b : ℝ, Convex ℝ {x | g x ≤ b})
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (b : ℝ) :
    cdf ((Measure.pi (fun _ : ι => gaussianReal 0 1)).map
      (fun z => g (L z + t • v))) b ≤
    cdf ((Measure.pi (fun _ : ι => gaussianReal 0 1)).map
      (fun z => g (L z + s • v))) b := by
  have hm (r : ℝ) : Measurable (fun z => g (L z + r • v)) := hgm.comp (by fun_prop)
  letI (r : ℝ) : IsProbabilityMeasure
      ((Measure.pi (fun _ : ι => gaussianReal 0 1)).map (fun z => g (L z + r • v))) :=
    by infer_instance
  rw [cdf_eq_real, cdf_eq_real, Measure.real, Measure.real,
    Measure.map_apply (hm t) measurableSet_Iic,
    Measure.map_apply (hm s) measurableSet_Iic]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  exact gaussian_anderson_ray L v (hgm measurableSet_Iic) (hconvex b)
    (fun x hx => by
      change g x ≤ b at hx
      change g (-x) ≤ b
      rw [heven]
      exact hx) hs hst

theorem lintegral_le_of_cdf_le {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : ℝ → ℝ≥0∞} (hfm : Measurable f) (hf : Monotone f)
    (horder : ∀ x, cdf ν x ≤ cdf μ x) :
    ∫⁻ x, f x ∂μ ≤ ∫⁻ x, f x ∂ν := by
  let coupling := μ.quantileCoupling ν
  have hc : TauCeti.IsCoupling coupling μ ν := μ.isCoupling_quantileCoupling ν
  have hle : (fun z : ℝ × ℝ => f z.1) ≤ᵐ[coupling] fun z => f z.2 := by
    filter_upwards [μ.ae_fst_le_snd_quantileCoupling ν horder] with z hz
    exact hf hz
  calc
    (∫⁻ x, f x ∂μ) = ∫⁻ z, f z.1 ∂coupling :=
      (hc.measurePreserving_fst.lintegral_comp hfm).symm
    _ ≤ ∫⁻ z, f z.2 ∂coupling := lintegral_mono_ae hle
    _ = ∫⁻ x, f x ∂ν := hc.measurePreserving_snd.lintegral_comp hfm

/-- Arbitrary nonnegative increasing outer functions preserve Anderson
comparison, including infinite expectations. -/
theorem lintegral_gaussian_even_quasiconvex_shift_le
    (L : (ι → ℝ) →L[ℝ] V) (v : V) {g : V → ℝ} (hgm : Measurable g)
    (heven : ∀ x, g (-x) = g x)
    (hconvex : ∀ b : ℝ, Convex ℝ {x | g x ≤ b})
    {f : ℝ → ℝ≥0∞} (hfm : Measurable f) (hf : Monotone f)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (∫⁻ z, f (g (L z + s • v)) ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) ≤
      ∫⁻ z, f (g (L z + t • v)) ∂Measure.pi (fun _ : ι => gaussianReal 0 1) := by
  have hm (r : ℝ) : Measurable (fun z => g (L z + r • v)) := hgm.comp (by fun_prop)
  letI (r : ℝ) : IsProbabilityMeasure
      ((Measure.pi (fun _ : ι => gaussianReal 0 1)).map (fun z => g (L z + r • v))) :=
    by infer_instance
  have h := lintegral_le_of_cdf_le hfm hf
    (cdf_gaussian_even_quasiconvex_shift_antitone L v hgm heven hconvex hs hst)
  simpa only [lintegral_map hfm (hm s), lintegral_map hfm (hm t)] using h

end Wishart
end
end CanonicalSource60

section CanonicalSource61
/- Source: Wishart/SpectralGauge.lean -/



/-!
# The exact convex spectral gauges of Theorem 5.2

The function is totalized on the ambient symmetric matrix space, while every
mathematical property and every application is restricted to the positive cone.
Values outside that cone never occur in a gauge conclusion.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification
open scoped Matrix MatrixOrder Matrix.Norms.Operator ENNReal

namespace Wishart

def positiveSemidefiniteCone (k : ℕ) : Set (SymmetricMatrix k) :=
  {X | (X : Matrix (Fin k) (Fin k) ℝ).PosSemidef}

theorem convex_positiveSemidefiniteCone (k : ℕ) :
    Convex ℝ (positiveSemidefiniteCone k) := by
  intro X hX Y hY a b ha hb hab
  exact (hX.smul ha).add (hY.smul hb)

/-- A nonzero continuous convex homogeneous Loewner-increasing orthogonally
invariant function on the positive semidefinite cone, precisely as defined in
the manuscript. The additional totalization outside the cone is immaterial. -/
structure SpectralGauge (k : ℕ) where
  toFun : SymmetricMatrix k → ℝ
  nonnegative : ∀ X ∈ positiveSemidefiniteCone k, 0 ≤ toFun X
  nonzero : ∃ X ∈ positiveSemidefiniteCone k, toFun X ≠ 0
  continuousOn : ContinuousOn toFun (positiveSemidefiniteCone k)
  convexOn : ConvexOn ℝ (positiveSemidefiniteCone k) toFun
  homogeneous : ∀ (a : ℝ), 0 ≤ a → ∀ X ∈ positiveSemidefiniteCone k,
    toFun (a • X) = a * toFun X
  loewner : ∀ X ∈ positiveSemidefiniteCone k, ∀ Y ∈ positiveSemidefiniteCone k,
    ((Y - X : SymmetricMatrix k) : Matrix (Fin k) (Fin k) ℝ).PosSemidef →
      toFun X ≤ toFun Y
  orthogonalInvariant : ∀ (U : Matrix.orthogonalGroup (Fin k) ℝ)
    (X : SymmetricMatrix k), X ∈ positiveSemidefiniteCone k →
    toFun (Matrix.symmetricCongruenceLinearMap (U : Matrix (Fin k) (Fin k) ℝ) X) =
      toFun X

instance {k : ℕ} : CoeFun (SpectralGauge k) (fun _ => SymmetricMatrix k → ℝ) :=
  ⟨SpectralGauge.toFun⟩

namespace SpectralGauge

variable {k : ℕ} (Φ : SpectralGauge k)

@[simp] theorem map_zero : Φ (0 : SymmetricMatrix k) = 0 := by
  simpa using Φ.homogeneous 0 le_rfl 0 Matrix.PosSemidef.zero

theorem rankOne_convexity_identity (u v : EuclideanSpace ℝ (Fin k))
    (a b : ℝ) (hab : a + b = 1) :
    a • rankOneSymmetric u + b • rankOneSymmetric v -
        rankOneSymmetric (a • u + b • v) =
      (a * b) • rankOneSymmetric (u - v) := by
  apply Subtype.ext
  ext i j
  simp only [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul,
    coe_rankOneSymmetric, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  have hb : b = 1 - a := by linarith
  subst b
  ring

theorem rankOne_convexity_difference_posSemidef (u v : EuclideanSpace ℝ (Fin k))
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ((a • rankOneSymmetric u + b • rankOneSymmetric v -
      rankOneSymmetric (a • u + b • v) : SymmetricMatrix k) :
      Matrix (Fin k) (Fin k) ℝ).PosSemidef := by
  rw [rankOne_convexity_identity u v a b hab]
  exact (rankOneSymmetric_posSemidef _).smul (mul_nonneg ha hb)

theorem continuous_rankOne_profile {B : SymmetricMatrix k}
    (hB : B ∈ positiveSemidefiniteCone k) :
    Continuous (fun u : EuclideanSpace ℝ (Fin k) => Φ (B + rankOneSymmetric u)) := by
  apply Φ.continuousOn.comp_continuous
  · exact continuous_const.add hasTemperateGrowth_rankOneSymmetric.1.continuous
  · intro u
    exact hB.add (rankOneSymmetric_posSemidef u)

theorem even_rankOne_profile (B : SymmetricMatrix k)
    (u : EuclideanSpace ℝ (Fin k)) :
    Φ (B + rankOneSymmetric (-u)) = Φ (B + rankOneSymmetric u) := by
  rw [rankOneSymmetric_neg]

theorem convexOn_rankOne_profile {B : SymmetricMatrix k}
    (hB : B ∈ positiveSemidefiniteCone k) :
    ConvexOn ℝ Set.univ
      (fun u : EuclideanSpace ℝ (Fin k) => Φ (B + rankOneSymmetric u)) := by
  refine ⟨convex_univ, ?_⟩
  intro u _ v _ a b ha hb hab
  have hu : B + rankOneSymmetric u ∈ positiveSemidefiniteCone k :=
    hB.add (rankOneSymmetric_posSemidef u)
  have hv : B + rankOneSymmetric v ∈ positiveSemidefiniteCone k :=
    hB.add (rankOneSymmetric_posSemidef v)
  have hm : a • (B + rankOneSymmetric u) + b • (B + rankOneSymmetric v) ∈
      positiveSemidefiniteCone k := convex_positiveSemidefiniteCone k hu hv ha hb hab
  have hdiff :
      ((a • (B + rankOneSymmetric u) + b • (B + rankOneSymmetric v) -
        (B + rankOneSymmetric (a • u + b • v)) : SymmetricMatrix k) :
        Matrix (Fin k) (Fin k) ℝ).PosSemidef := by
    have heq : a • (B + rankOneSymmetric u) + b • (B + rankOneSymmetric v) -
        (B + rankOneSymmetric (a • u + b • v)) =
        a • rankOneSymmetric u + b • rankOneSymmetric v -
          rankOneSymmetric (a • u + b • v) := by
      rw [smul_add, smul_add]
      have hB' : a • B + b • B = B := by rw [← add_smul, hab, one_smul]
      calc
        _ = (a • B + b • B) +
            (a • rankOneSymmetric u + b • rankOneSymmetric v) -
            (B + rankOneSymmetric (a • u + b • v)) := by abel
        _ = _ := by rw [hB']; abel
    rw [heq]
    exact rankOne_convexity_difference_posSemidef u v ha hb hab
  exact (Φ.loewner _ (hB.add (rankOneSymmetric_posSemidef _)) _ hm hdiff).trans
    (Φ.convexOn.2 hu hv ha hb hab)

theorem convex_sublevel_rankOne_profile {B : SymmetricMatrix k}
    (hB : B ∈ positiveSemidefiniteCone k) (c : ℝ) :
    Convex ℝ {u : EuclideanSpace ℝ (Fin k) | Φ (B + rankOneSymmetric u) ≤ c} := by
  simpa only [Set.mem_univ, true_and] using (Φ.convexOn_rankOne_profile hB).convex_le c

theorem cdf_rectangularGaussian_rankOne_antitone {m : ℕ}
    {B : SymmetricMatrix k} (hB : B ∈ positiveSemidefiniteCone k)
    (L : Matrix (Fin k) (Fin m) ℝ) (v : EuclideanSpace ℝ (Fin k))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (c : ℝ) :
    cdf ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) 1).map
      (fun z => Φ (B + rankOneSymmetric (L.toEuclideanLin z + Real.sqrt t • v)))) c ≤
    cdf ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) 1).map
      (fun z => Φ (B + rankOneSymmetric (L.toEuclideanLin z + Real.sqrt s • v)))) c := by
  let L' : (Fin m → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
    L.toEuclideanLin.toContinuousLinearMap.comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.toContinuousLinearMap
  have hlaw (r : ℝ) :
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) 1).map
        (fun z => Φ (B + rankOneSymmetric (L.toEuclideanLin z + Real.sqrt r • v))) =
      (Measure.pi (fun _ : Fin m => gaussianReal 0 1)).map
        (fun z => Φ (B + rankOneSymmetric (L' z + Real.sqrt r • v))) := by
    rw [multivariateGaussian_one_eq_map_pi]
    simp only [PiLp.zero_apply]
    rw [Measure.map_map]
    · rfl
    · exact (Φ.continuous_rankOne_profile hB).measurable.comp (by fun_prop)
    · fun_prop
  rw [hlaw t, hlaw s]
  exact cdf_gaussian_even_quasiconvex_shift_antitone L' v
    (Φ.continuous_rankOne_profile hB).measurable (Φ.even_rankOne_profile B)
    (Φ.convex_sublevel_rankOne_profile hB) (Real.sqrt_nonneg s) (Real.sqrt_le_sqrt hst) c

/-- No condition on the residual Wishart degree is needed for a single gauge:
the conditional Gaussian comparison works for every PSD background. -/
theorem integral_rectangularGaussian_rankOne_le {m : ℕ}
    {B : SymmetricMatrix k} (hB : B ∈ positiveSemidefiniteCone k)
    (L : Matrix (Fin k) (Fin m) ℝ) (v : EuclideanSpace ℝ (Fin k))
    {f : ℝ → ℝ} (hfm : Measurable f) (hf : MonotoneOn f (Set.Ici 0))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (hsi : Integrable (fun z => f (Φ (B + rankOneSymmetric
      (L.toEuclideanLin z + Real.sqrt s • v)))) (multivariateGaussian 0 1))
    (hti : Integrable (fun z => f (Φ (B + rankOneSymmetric
      (L.toEuclideanLin z + Real.sqrt t • v)))) (multivariateGaussian 0 1)) :
    (∫ z, f (Φ (B + rankOneSymmetric (L.toEuclideanLin z + Real.sqrt s • v)))
      ∂multivariateGaussian 0 1) ≤
      ∫ z, f (Φ (B + rankOneSymmetric (L.toEuclideanLin z + Real.sqrt t • v)))
        ∂multivariateGaussian 0 1 := by
  let F (r : ℝ) (z : EuclideanSpace ℝ (Fin m)) :=
    Φ (B + rankOneSymmetric (L.toEuclideanLin z + Real.sqrt r • v))
  have hm (r : ℝ) : Measurable (F r) :=
    (Φ.continuous_rankOne_profile hB).measurable.comp (by fun_prop)
  let law (r : ℝ) := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) 1).map (F r)
  letI (r : ℝ) : IsProbabilityMeasure (law r) := by infer_instance
  have hsupport (r : ℝ) : ∀ᵐ x ∂law r, x ∈ Set.Ici 0 := by
    change ∀ᵐ x ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) 1).map (F r),
      0 ≤ x
    rw [ae_map_iff (hm r).aemeasurable measurableSet_Ici]
    exact Filter.Eventually.of_forall fun z =>
      Φ.nonnegative _ (hB.add (rankOneSymmetric_posSemidef _))
  have hsi' : Integrable f (law s) :=
    (integrable_map_measure hfm.aestronglyMeasurable (hm s).aemeasurable).mpr hsi
  have hti' : Integrable f (law t) :=
    (integrable_map_measure hfm.aestronglyMeasurable (hm t).aemeasurable).mpr hti
  have h := WishartVerification.integral_le_of_cdf_le_on_support hf
    (hsupport s) (hsupport t) hsi' hti'
    (Φ.cdf_rectangularGaussian_rankOne_antitone hB L v hs hst)
  simpa only [law, integral_map (hm s).aemeasurable hfm.aestronglyMeasurable,
    integral_map (hm t).aemeasurable hfm.aestronglyMeasurable] using h

end SpectralGauge

end Wishart
end
end CanonicalSource61

section CanonicalSource62
/- Source: Wishart/PositiveGaugeSupport.lean -/



/-!
# Positive supporting functionals of a convex spectral gauge

The existence of a positive support is derived from geometric Hahn–Banach.
At a positive definite matrix the epigraph has nonempty interior, its vertical
support coefficient is strictly negative, and monotonicity makes the normalized
support positive on every positive semidefinite direction. Homogeneity removes
the affine constant.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti
open WishartVerification Filter Set Topology
open scoped Matrix MatrixOrder Matrix.Norms.Operator RealInnerProductSpace InnerProductSpace

namespace Wishart

theorem exists_pos_of_eventually_zero {P : ℝ → Prop} (hP : ∀ᶠ t in 𝓝 (0 : ℝ), P t) :
    ∃ t : ℝ, 0 < t ∧ P t := by
  have hP' : ∀ᶠ t in 𝓝[>] (0 : ℝ), P t := hP.filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  exact (hpos.and hP').exists

namespace SpectralGauge

variable {k : ℕ} (Φ : SpectralGauge k)

-- The symmetric carrier has TauCeti's Frobenius structure.  Select its
-- seminormed parent explicitly, rather than the ambient operator-norm subtype
-- instance, so Riesz representation and the trace pairing use the same norm.
local instance gaugeSymmetricSeminormedAddCommGroup :
    SeminormedAddCommGroup (SymmetricMatrix k) :=
  (TauCeti.symmetricMatrixNormedAddCommGroup k).toSeminormedAddCommGroup

local instance gaugeSymmetricInnerProductSpace :
    InnerProductSpace ℝ (SymmetricMatrix k) :=
  TauCeti.symmetricMatrixInnerProductSpace k

theorem continuousAt_of_posDef {Q : SymmetricMatrix k}
    (hQ : (Q : Matrix (Fin k) (Fin k) ℝ).PosDef) : ContinuousAt Φ Q := by
  have hc : ContinuousOn Φ
      {X : SymmetricMatrix k | (X : Matrix (Fin k) (Fin k) ℝ).PosDef} :=
    Φ.continuousOn.mono (fun X (hX : (X : Matrix (Fin k) (Fin k) ℝ).PosDef) => hX.posSemidef)
  apply (hc Q hQ).continuousAt
  exact (TauCeti.isOpen_setOfPred_posDefMatrix k).mem_nhds hQ

/-- An actual subgradient at each interior point of the PSD cone. -/
theorem exists_subgradient_of_posDef {Q : SymmetricMatrix k}
    (hQ : (Q : Matrix (Fin k) (Fin k) ℝ).PosDef) :
    ∃ l : SymmetricMatrix k →L[ℝ] ℝ,
      ∀ X ∈ positiveSemidefiniteCone k, Φ Q + l (X - Q) ≤ Φ X := by
  let E : Set (SymmetricMatrix k × ℝ) :=
    {z | z.1 ∈ positiveSemidefiniteCone k ∧ Φ z.1 ≤ z.2}
  have hE : Convex ℝ E := Φ.convexOn.convex_epigraph
  have hnot : (Q, Φ Q) ∉ interior E := by
    intro hmem
    have ht : Tendsto (fun r : ℝ => (Q, Φ Q - r)) (𝓝 0) (𝓝 (Q, Φ Q)) := by
      have hc : Continuous (fun r : ℝ => (Q, Φ Q - r)) := by fun_prop
      simpa only [sub_zero] using
        hc.continuousAt.tendsto (x := 0)
    have hnear : ∀ᶠ r : ℝ in 𝓝 0, (Q, Φ Q - r) ∈ E :=
      ht.eventually (mem_interior_iff_mem_nhds.mp hmem)
    obtain ⟨r, hr, hEr⟩ := exists_pos_of_eventually_zero hnear
    have hineq : Φ Q ≤ Φ Q - r := hEr.2
    linarith
  have hinterior : (Q, Φ Q + 1) ∈ interior E := by
    apply mem_interior_iff_mem_nhds.mpr
    have hpd : ∀ᶠ z : SymmetricMatrix k × ℝ in 𝓝 (Q, Φ Q + 1),
        (z.1 : Matrix (Fin k) (Fin k) ℝ).PosDef :=
      continuous_fst.continuousAt.eventually
        ((TauCeti.isOpen_setOfPred_posDefMatrix k).mem_nhds hQ)
    have hstrict : ∀ᶠ z : SymmetricMatrix k × ℝ in 𝓝 (Q, Φ Q + 1), Φ z.1 < z.2 :=
      ((Φ.continuousAt_of_posDef hQ).comp continuous_fst.continuousAt).eventually_lt
        continuous_snd.continuousAt (by change Φ Q < Φ Q + 1; linarith)
    filter_upwards [hpd, hstrict] with z hz hlt
    exact ⟨hz.posSemidef, hlt.le⟩
  obtain ⟨F, hFne, hF⟩ := geometric_hahn_banach_of_nonempty_interior_point
    hE hnot ⟨_, hinterior⟩
  let l₀ : SymmetricMatrix k →L[ℝ] ℝ :=
    F.comp (ContinuousLinearMap.inl ℝ (SymmetricMatrix k) ℝ)
  let c : ℝ := F (0, 1)
  have hsplit (X : SymmetricMatrix k) (t : ℝ) : F (X, t) = l₀ X + t * c := by
    have heq : (X, t) = (X, 0) + t • (0, 1) := by ext <;> simp
    rw [heq, map_add, map_smul]
    simp only [l₀, c, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      smul_eq_mul]
  have hc : c ≤ 0 := by
    have h := hF (Q, Φ Q + 1) ⟨hQ.posSemidef, by linarith⟩
    rw [hsplit, hsplit] at h
    linarith
  have hcstrict : c < 0 := by
    by_contra hcnot
    have hc0 : c = 0 := le_antisymm hc (not_lt.mp hcnot)
    have hlocal : IsLocalMax l₀ Q := by
      filter_upwards [(TauCeti.isOpen_setOfPred_posDefMatrix k).mem_nhds hQ] with X hX
      have h := hF (X, Φ X) ⟨hX.posSemidef, le_rfl⟩
      simpa only [hsplit, hc0, mul_zero, add_zero] using h
    have hl0 : l₀ = 0 := hlocal.hasFDerivAt_eq_zero l₀.hasFDerivAt
    apply hFne
    apply ContinuousLinearMap.ext
    intro z
    rcases z with ⟨X, t⟩
    change F (X, t) = 0
    rw [hsplit, hc0, hl0]
    simp only [ContinuousLinearMap.zero_apply, mul_zero, add_zero]
  let l : SymmetricMatrix k →L[ℝ] ℝ := (-c)⁻¹ • l₀
  refine ⟨l, fun X hX => ?_⟩
  have h := hF (X, Φ X) ⟨hX, le_rfl⟩
  rw [hsplit, hsplit] at h
  have hpos : 0 < -c := neg_pos.mpr hcstrict
  change Φ Q + (-c)⁻¹ * l₀ (X - Q) ≤ Φ X
  rw [map_sub]
  apply (mul_le_mul_iff_right₀ hpos).mp
  have hcancel : (-c) * ((-c)⁻¹ * (l₀ X - l₀ Q)) = l₀ X - l₀ Q := by
    rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
  rw [mul_add, hcancel]
  nlinarith

/-- Homogeneity turns the supporting affine function into a linear minorant
that equals the gauge at the selected positive definite matrix. -/
theorem exists_positive_linear_support {Q : SymmetricMatrix k}
    (hQ : (Q : Matrix (Fin k) (Fin k) ℝ).PosDef) :
    ∃ l : SymmetricMatrix k →L[ℝ] ℝ,
      l Q = Φ Q ∧
      (∀ X ∈ positiveSemidefiniteCone k, l X ≤ Φ X) ∧
      (∀ D ∈ positiveSemidefiniteCone k, 0 ≤ l D) := by
  obtain ⟨l, hl⟩ := Φ.exists_subgradient_of_posDef hQ
  have hzero := hl 0 Matrix.PosSemidef.zero
  have htwo := hl ((2 : ℝ) • Q) (hQ.posSemidef.smul (by norm_num : (0 : ℝ) ≤ 2))
  have hcontact : l Q = Φ Q := by
    simp only [map_zero, zero_sub, map_neg, Φ.map_zero] at hzero
    rw [Φ.homogeneous 2 (by norm_num) Q hQ.posSemidef,
      map_sub, map_smul, smul_eq_mul] at htwo
    linarith
  have hminor (X : SymmetricMatrix k) (hX : X ∈ positiveSemidefiniteCone k) :
      l X ≤ Φ X := by
    have h := hl X hX
    rw [map_sub, hcontact] at h
    linarith
  refine ⟨l, hcontact, hminor, fun D hD => ?_⟩
  have hnear : ∀ᶠ t : ℝ in 𝓝 0,
      ((Q - t • D : SymmetricMatrix k) : Matrix (Fin k) (Fin k) ℝ).PosDef := by
    have ht : Tendsto (fun t : ℝ => Q - t • D) (𝓝 0) (𝓝 Q) := by
      have hc : Continuous (fun t : ℝ => Q - t • D) := by fun_prop
      simpa only [zero_smul, sub_zero] using
        hc.continuousAt.tendsto (x := 0)
    exact ht.eventually ((TauCeti.isOpen_setOfPred_posDefMatrix k).mem_nhds hQ)
  obtain ⟨t, ht, hQt⟩ := exists_pos_of_eventually_zero hnear
  have hle : Φ (Q - t • D) ≤ Φ Q :=
    Φ.loewner _ hQt.posSemidef Q hQ.posSemidef (by
      simpa only [sub_sub_cancel, Submodule.coe_smul] using hD.smul ht.le)
  have hs := (hminor _ hQt.posSemidef).trans hle
  rw [map_sub, map_smul, smul_eq_mul, hcontact] at hs
  nlinarith

def identitySymmetric (k : ℕ) : SymmetricMatrix k :=
  ⟨1, Matrix.isHermitian_one.isSelfAdjoint⟩

@[simp] theorem coe_identitySymmetric :
    (identitySymmetric k : Matrix (Fin k) (Fin k) ℝ) = 1 := rfl

theorem norm_le_trace_of_posSemidef {H : SymmetricMatrix k}
    (hH : (H : Matrix (Fin k) (Fin k) ℝ).PosSemidef) :
    ‖H‖ ≤ (H : Matrix (Fin k) (Fin k) ℝ).trace := by
  have hsq : ‖H‖ ^ 2 = ((H : Matrix (Fin k) (Fin k) ℝ) ^ 2).trace := by
    calc
      ‖H‖ ^ 2 = inner ℝ H H := (real_inner_self_eq_norm_sq H).symm
      _ = ((H : Matrix (Fin k) (Fin k) ℝ) * H).trace := selfAdjoint.inner_eq_trace_mul H H
      _ = _ := by rw [pow_two]
  have hbound : ((H : Matrix (Fin k) (Fin k) ℝ) ^ 2).trace ≤
      (H : Matrix (Fin k) (Fin k) ℝ).trace ^ 2 := by
    rw [hH.isHermitian.trace_pow_eq_sum_eigenvalues_pow,
      hH.isHermitian.trace_eq_sum_eigenvalues]
    simpa using
      Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (fun i _ => hH.eigenvalues_nonneg i)
  have htrace := hH.trace_nonneg
  have hnorm := norm_nonneg H
  nlinarith

/-- Riesz representation gives the positive matrix in the manuscript's trace
support formula. Positivity is proved by testing all rank-one matrices. -/
theorem exists_trace_support_of_posDef {Q : SymmetricMatrix k}
    (hQ : (Q : Matrix (Fin k) (Fin k) ℝ).PosDef) :
    ∃ H : SymmetricMatrix k,
      (H : Matrix (Fin k) (Fin k) ℝ).PosSemidef ∧
      ⟪H, Q⟫_ℝ = Φ Q ∧
      ∀ X ∈ positiveSemidefiniteCone k, ⟪H, X⟫_ℝ ≤ Φ X := by
  obtain ⟨l, hcontact, hminor, hpositive⟩ := Φ.exists_positive_linear_support hQ
  let H : SymmetricMatrix k := (InnerProductSpace.toDual ℝ (SymmetricMatrix k)).symm l
  have hrepr (X : SymmetricMatrix k) : ⟪H, X⟫_ℝ = l X :=
    InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := SymmetricMatrix k) (x := X) (y := l)
  refine ⟨H, ?_, (hrepr Q).trans hcontact, fun X hX => (hrepr X).le.trans (hminor X hX)⟩
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (selfAdjoint.isHermitian_coe H)
  intro u
  have h := hpositive (rankOneSymmetric (WithLp.toLp 2 u))
    (rankOneSymmetric_posSemidef _)
  rw [← hrepr, selfAdjoint.inner_eq_trace_mul, coe_rankOneSymmetric,
    Matrix.trace_mul_comm, trace_mul_rankOne] at h
  simpa only [PiLp.toLp_apply, star_trivial] using h

/-- The canonical compact set of all positive linear trace minorants. -/
def supportSet : Set (SymmetricMatrix k) :=
  {H | (H : Matrix (Fin k) (Fin k) ℝ).PosSemidef ∧
    ∀ X ∈ positiveSemidefiniteCone k, ⟪H, X⟫_ℝ ≤ Φ X}

theorem zero_mem_supportSet : (0 : SymmetricMatrix k) ∈ Φ.supportSet := by
  refine ⟨Matrix.PosSemidef.zero, fun X hX => ?_⟩
  simpa only [inner_zero_left] using Φ.nonnegative X hX

theorem supportSet_nonempty : Φ.supportSet.Nonempty := ⟨0, Φ.zero_mem_supportSet⟩

theorem isClosed_supportSet : IsClosed Φ.supportSet := by
  change IsClosed
    ({H : SymmetricMatrix k | (H : Matrix (Fin k) (Fin k) ℝ).PosSemidef} ∩
      {H : SymmetricMatrix k | ∀ X ∈ positiveSemidefiniteCone k, ⟪H, X⟫_ℝ ≤ Φ X})
  apply IsClosed.inter
  · exact Matrix.posSemidef_is_closed.preimage continuous_subtype_val
  · simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro X
    apply isClosed_iInter
    intro hX
    exact isClosed_le (continuous_id.inner continuous_const) continuous_const

theorem trace_le_of_mem_supportSet {H : SymmetricMatrix k} (hH : H ∈ Φ.supportSet) :
    (H : Matrix (Fin k) (Fin k) ℝ).trace ≤ Φ (identitySymmetric k) := by
  have h := hH.2 (identitySymmetric k) Matrix.PosSemidef.one
  simpa only [selfAdjoint.inner_eq_trace_mul, coe_identitySymmetric, Matrix.one_mul] using h

theorem isCompact_supportSet : IsCompact Φ.supportSet := by
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  refine ⟨Φ.isClosed_supportSet, isBounded_iff_forall_norm_le.mpr ?_⟩
  exact ⟨Φ (identitySymmetric k), fun H hH =>
    (norm_le_trace_of_posSemidef hH.1).trans (Φ.trace_le_of_mem_supportSet hH)⟩

/-- Exact support representation, including singular matrices on the boundary
of the PSD cone. Compactness ensures that the supremum is attained. -/
theorem exists_support_attaining {X : SymmetricMatrix k}
    (hX : X ∈ positiveSemidefiniteCone k) :
    ∃ H ∈ Φ.supportSet, ⟪H, X⟫_ℝ = Φ X := by
  have hc : Continuous (fun H : SymmetricMatrix k => ⟪H, X⟫_ℝ) :=
    continuous_id.inner continuous_const
  obtain ⟨H, hH, hmax⟩ := Φ.isCompact_supportSet.exists_isMaxOn Φ.supportSet_nonempty
    hc.continuousOn
  refine ⟨H, hH, le_antisymm (hH.2 X hX) ?_⟩
  let I := identitySymmetric k
  have hbound (t : ℝ) (ht : 0 < t) :
      Φ (X + t • I) - t * Φ I ≤ ⟪H, X⟫_ℝ := by
    have hpos : ((X + t • I : SymmetricMatrix k) : Matrix (Fin k) (Fin k) ℝ).PosDef :=
      Matrix.PosDef.posSemidef_add hX (Matrix.PosDef.one.smul ht)
    obtain ⟨Ht, hHt, hcontact, hminor⟩ := Φ.exists_trace_support_of_posDef hpos
    have hHtK : Ht ∈ Φ.supportSet := ⟨hHt, hminor⟩
    have hmax' : ⟪Ht, X⟫_ℝ ≤ ⟪H, X⟫_ℝ := hmax hHtK
    have hI := hminor I Matrix.PosSemidef.one
    rw [inner_add_right, real_inner_smul_right] at hcontact
    have hmul := mul_le_mul_of_nonneg_left hI ht.le
    linarith
  have hpath : Tendsto (fun t : ℝ => X + t • I) (𝓝[>] 0)
      (𝓝[positiveSemidefiniteCone k] X) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have h : Tendsto (fun t : ℝ => X + t • I) (𝓝 0) (𝓝 X) := by
        have hc : Continuous (fun t : ℝ => X + t • I) := by fun_prop
        simpa only [zero_smul, add_zero] using
          hc.continuousAt.tendsto (x := 0)
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact hX.add (Matrix.PosSemidef.one.smul ht.le)
  have hlim : Tendsto (fun t : ℝ => Φ (X + t • I) - t * Φ I)
      (𝓝[>] 0) (𝓝 (Φ X)) := by
    have hΦ : Tendsto Φ (𝓝[positiveSemidefiniteCone k] X) (𝓝 (Φ X)) :=
      Φ.continuousOn X hX
    simpa only [Function.comp_apply, id_eq, zero_mul, sub_zero] using
      (Filter.Tendsto.comp hΦ hpath).sub
        ((tendsto_id.mono_left nhdsWithin_le_nhds).mul tendsto_const_nhds)
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact hbound t ht

/-- The formula `Φ(Q) = max_H tr(HQ)` in its attained form. -/
theorem exists_trace_attaining {X : SymmetricMatrix k}
    (hX : X ∈ positiveSemidefiniteCone k) :
    ∃ H ∈ Φ.supportSet,
      ((H : Matrix (Fin k) (Fin k) ℝ) * (X : Matrix (Fin k) (Fin k) ℝ)).trace = Φ X := by
  obtain ⟨H, hH, heq⟩ := Φ.exists_support_attaining hX
  refine ⟨H, hH, ?_⟩
  exact (Matrix.trace_mul_comm (H : Matrix (Fin k) (Fin k) ℝ)
    (X : Matrix (Fin k) (Fin k) ℝ)).trans
      ((selfAdjoint.inner_eq_trace_mul H X).symm.trans heq)

/-- A single countable family of positive trace minorants recovers the gauge
at every PSD input. This supplies finite maxima for subsequent regularization. -/
theorem exists_countable_positive_support :
    ∃ H : ℕ → SymmetricMatrix k,
      (∀ n, H n ∈ Φ.supportSet) ∧
      ∀ X ∈ positiveSemidefiniteCone k, (⨆ n, ⟪H n, X⟫_ℝ) = Φ X := by
  letI : Nonempty Φ.supportSet := ⟨⟨0, Φ.zero_mem_supportSet⟩⟩
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq Φ.supportSet
  refine ⟨fun n => (u n : SymmetricMatrix k), fun n => (u n).2, fun X hX => ?_⟩
  have hb : BddAbove (Set.range (fun n => ⟪(u n : SymmetricMatrix k), X⟫_ℝ)) :=
    ⟨Φ X, by rintro _ ⟨n, rfl⟩; exact (u n).2.2 X hX⟩
  apply le_antisymm (ciSup_le fun n => (u n).2.2 X hX)
  by_contra hnot
  have hlt : (⨆ n, ⟪(u n : SymmetricMatrix k), X⟫_ℝ) < Φ X := lt_of_not_ge hnot
  obtain ⟨H, hH, heq⟩ := Φ.exists_support_attaining hX
  let O : Set Φ.supportSet :=
    {z | (⨆ n, ⟪(u n : SymmetricMatrix k), X⟫_ℝ) < ⟪(z : SymmetricMatrix k), X⟫_ℝ}
  have hO : IsOpen O := isOpen_lt continuous_const (continuous_subtype_val.inner continuous_const)
  have hOne : O.Nonempty := ⟨⟨H, hH⟩, by simpa only [O, Set.mem_setOf_eq, heq] using hlt⟩
  obtain ⟨n, hn⟩ := hu.exists_mem_open hO hOne
  exact (le_ciSup hb n).not_gt hn

end SpectralGauge

end Wishart
end
end CanonicalSource62

section CanonicalSource63
/- Source: Wishart/PositiveTraceBounds.lean -/



/-! # Dimension-free bounds for positive trace forms -/

noncomputable section

open Matrix Unitary
open scoped MatrixOrder

namespace WishartVerification

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem trace_smul_one_sub_posSemidef {B : Matrix n n ℝ} (hB : B.PosSemidef) :
    (B.trace • (1 : Matrix n n ℝ) - B).PosSemidef := by
  let d := hB.isHermitian.eigenvalues
  have hd (i : n) : 0 ≤ B.trace - d i := by
    rw [hB.isHermitian.trace_eq_sum_eigenvalues]
    exact sub_nonneg.mpr (Finset.single_le_sum
      (fun j _ => hB.eigenvalues_nonneg j) (Finset.mem_univ i))
  have hdiag : (Matrix.diagonal (fun i => B.trace - d i)).PosSemidef :=
    Matrix.PosSemidef.diagonal hd
  have heq : B.trace • (1 : Matrix n n ℝ) - B =
      conjStarAlgAut ℝ _ hB.isHermitian.eigenvectorUnitary
        (Matrix.diagonal (fun i => B.trace - d i)) := by
    have h : (Matrix.diagonal (fun i => B.trace - d i)) =
        B.trace • (1 : Matrix n n ℝ) -
          Matrix.diagonal (RCLike.ofReal ∘ hB.isHermitian.eigenvalues) := by
      simp [d, ← Matrix.diagonal_one, ← Matrix.diagonal_sub, ← Matrix.diagonal_smul,
        Pi.smul_def]
    rw [h, map_sub, map_smul, map_one, ← hB.isHermitian.spectral_theorem]
  rw [heq]
  simpa only [conjStarAlgAut_apply, Unitary.coe_star, Matrix.star_eq_conjTranspose] using
    hdiag.mul_mul_conjTranspose_same
      (hB.isHermitian.eigenvectorUnitary : Matrix n n ℝ)

theorem trace_mul_smul_sub_sandwich_posSemidef {D X : Matrix n n ℝ}
    (hD : D.PosSemidef) (hX : X.PosSemidef) :
    ((D * X).trace • D - D * X * D).PosSemidef := by
  let R := CFC.sqrt D
  let B := R * X * R
  have hR : R.PosSemidef := Matrix.LE.le.posSemidef (CFC.sqrt_nonneg D)
  have hRR : R * R = D := CFC.sqrt_mul_sqrt_self D hD.nonneg
  have hB : B.PosSemidef := by
    simpa only [hR.isHermitian.eq] using hX.mul_mul_conjTranspose_same R
  have h := (trace_smul_one_sub_posSemidef hB).mul_mul_conjTranspose_same R
  rw [hR.isHermitian.eq, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hRR] at h
  have htrace : B.trace = (D * X).trace := by
    exact (hD.trace_sqrt_mul_mul_sqrt X).trans (Matrix.trace_mul_comm X D)
  have hsandwich : R * B * R = D * X * D := by
    calc
      R * B * R = (R * R) * X * (R * R) := by dsimp [B]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hRR]
  simpa only [htrace, hsandwich] using h

/-- The dimension-free quadratic bound used in equation (14). -/
theorem positive_trace_quadratic_bound {D X : Matrix n n ℝ}
    (hD : D.PosSemidef) (hX : X.PosSemidef) (v : n → ℝ) :
    (D *ᵥ v) ⬝ᵥ (X *ᵥ (D *ᵥ v)) ≤
      (v ⬝ᵥ (D *ᵥ v)) * (D * X).trace := by
  have h := (trace_mul_smul_sub_sandwich_posSemidef hD hX).dotProduct_mulVec_nonneg v
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul] at h
  have hquadratic : v ⬝ᵥ ((D * X * D) *ᵥ v) =
      (D *ᵥ v) ⬝ᵥ (X *ᵥ (D *ᵥ v)) := by
    simp only [← Matrix.mulVec_mulVec]
    rw [(Matrix.isHermitian_iff_isSymm.mp hD.isHermitian).dotProduct_mulVec_comm,
      dotProduct_comm]
  rw [hquadratic] at h
  nlinarith

theorem positive_affine_log_generator_lower_bound {D X A : Matrix n n ℝ}
    (hD : D.PosSemidef) (hX : X.PosSemidef) (hA : A.PosSemidef)
    {ε : ℝ} (hε : 0 < ε) (N : ℝ) (v : n → ℝ) :
    let Q := ε + (D * (A + X)).trace
    2 * (N - 2) * (v ⬝ᵥ (D *ᵥ v)) / Q ≤
      2 * N * (v ⬝ᵥ (D *ᵥ v)) / Q -
        4 * ((D *ᵥ v) ⬝ᵥ (X *ᵥ (D *ᵥ v))) / Q ^ 2 := by
  dsimp only
  let Q := ε + (D * (A + X)).trace
  have hQ : 0 < Q := add_pos_of_pos_of_nonneg hε
    (trace_mul_nonneg_of_posSemidef hD (hA.add hX))
  have hq : 0 ≤ v ⬝ᵥ (D *ᵥ v) := by simpa only [star_trivial] using hD.dotProduct_mulVec_nonneg v
  have htrace : (D * X).trace ≤ Q := by
    have hpos := trace_mul_nonneg_of_posSemidef hD hA
    dsimp [Q]
    rw [Matrix.mul_add, Matrix.trace_add]
    linarith
  have hbound := (positive_trace_quadratic_bound hD hX v).trans
    (mul_le_mul_of_nonneg_left htrace hq)
  change 2 * (N - 2) * (v ⬝ᵥ (D *ᵥ v)) / Q ≤
    2 * N * (v ⬝ᵥ (D *ᵥ v)) / Q -
      4 * ((D *ᵥ v) ⬝ᵥ (X *ᵥ (D *ᵥ v))) / Q ^ 2
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hQ)).mp
  field_simp [hQ.ne']
  nlinarith

end WishartVerification
end
end CanonicalSource63

section CanonicalSource64
/- Source: Wishart/GaugeBounds.lean -/



/-! # Positivity, measurable totalization, and actual gauge moment bounds -/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti
open WishartVerification Filter Set Topology
open scoped Matrix MatrixOrder Matrix.Norms.Operator

namespace Wishart.SpectralGauge

variable {k : ℕ} (Φ : SpectralGauge k)

theorem le_identity_mul_trace {X : SymmetricMatrix k}
    (hX : X ∈ positiveSemidefiniteCone k) :
    Φ X ≤ Φ (identitySymmetric k) * (X : Matrix (Fin k) (Fin k) ℝ).trace := by
  have hbound := trace_smul_one_sub_posSemidef hX
  have h := Φ.loewner X hX
    ((X : Matrix (Fin k) (Fin k) ℝ).trace • identitySymmetric k)
    (Matrix.PosSemidef.one.smul hX.trace_nonneg) hbound
  rw [Φ.homogeneous _ hX.trace_nonneg _ Matrix.PosSemidef.one] at h
  simpa only [mul_comm] using h

theorem identity_pos : 0 < Φ (identitySymmetric k) := by
  have hnonneg := Φ.nonnegative (identitySymmetric k) Matrix.PosSemidef.one
  apply lt_of_le_of_ne hnonneg
  intro hzero
  obtain ⟨X, hX, hne⟩ := Φ.nonzero
  have hupper := Φ.le_identity_mul_trace hX
  rw [← hzero, zero_mul] at hupper
  exact hne (le_antisymm hupper (Φ.nonnegative X hX))

theorem positive_of_posDef {X : SymmetricMatrix k}
    (hX : (X : Matrix (Fin k) (Fin k) ℝ).PosDef) : 0 < Φ X := by
  have hnear : ∀ᶠ t : ℝ in 𝓝 0,
      ((X - t • identitySymmetric k : SymmetricMatrix k) :
        Matrix (Fin k) (Fin k) ℝ).PosDef := by
    have ht : Tendsto (fun t : ℝ => X - t • identitySymmetric k) (𝓝 0) (𝓝 X) := by
      have hc : Continuous (fun t : ℝ => X - t • identitySymmetric k) := by fun_prop
      simpa only [zero_smul, sub_zero] using
        hc.continuousAt.tendsto (x := 0)
    exact ht.eventually ((TauCeti.isOpen_setOfPred_posDefMatrix k).mem_nhds hX)
  obtain ⟨t, ht, hXt⟩ := exists_pos_of_eventually_zero hnear
  have hle := Φ.loewner (t • identitySymmetric k)
    (Matrix.PosSemidef.one.smul ht.le) X hX.posSemidef hXt.posSemidef
  rw [Φ.homogeneous t ht.le _ Matrix.PosSemidef.one] at hle
  exact (mul_pos ht Φ.identity_pos).trans_le hle

/-- A measurable extension used only to express random variables on the whole
ambient measurable space. It equals the original gauge at every PSD matrix. -/
def value (X : SymmetricMatrix k) : ℝ :=
  (positiveSemidefiniteCone k).indicator Φ X

@[simp] theorem value_eq {X : SymmetricMatrix k} (hX : X ∈ positiveSemidefiniteCone k) :
    Φ.value X = Φ X := Set.indicator_of_mem hX _

@[fun_prop] theorem measurable_value : Measurable Φ.value := by
  classical
  apply Φ.continuousOn.measurable_piecewise continuousOn_const
  exact (Matrix.posSemidef_is_closed.preimage continuous_subtype_val).measurableSet

theorem value_nonneg (X : SymmetricMatrix k) : 0 ≤ Φ.value X := by
  classical
  by_cases hX : X ∈ positiveSemidefiniteCone k
  · rw [Φ.value_eq hX]
    exact Φ.nonnegative X hX
  · simp only [value, Set.indicator_of_notMem hX]
    exact le_rfl

theorem allFiniteMoments_value {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → SymmetricMatrix k} (hXm : Measurable X)
    (hX : ∀ᵐ z ∂μ, X z ∈ positiveSemidefiniteCone k)
    (hentries : ∀ i j, HasAllFiniteMoments
      (fun z => (X z : Matrix (Fin k) (Fin k) ℝ) i j) μ) :
    HasAllFiniteMoments (fun z => Φ.value (X z)) μ := by
  have htrace : HasAllFiniteMoments
      (fun z => (X z : Matrix (Fin k) (Fin k) ℝ).trace) μ :=
    HasAllFiniteMoments.finset_sum Finset.univ _ (fun i _ => hentries i i)
  intro q hq
  apply (htrace.const_mul (Φ (identitySymmetric k)) q hq).mono'
    (Φ.measurable_value.comp hXm).aestronglyMeasurable
  filter_upwards [hX] with z hz
  simp only [Function.comp_apply]
  rw [Real.norm_of_nonneg (Φ.value_nonneg _), Φ.value_eq hz]
  exact Φ.le_identity_mul_trace hz

end Wishart.SpectralGauge
end
end CanonicalSource64

section CanonicalSource65
/- Source: Wishart/PositivePrimitiveMeans.lean -/



/-!
# Power means of positive smooth primitives

This analytic closure theorem applies to concrete positive regularizations.
It proves the derivative and integrability infrastructure once, independently
of whether the primitives come from trace supports or determinant monomials.
The generator hypothesis is an auxiliary closure premise and is discharged
by the concrete trace and compression calculations in its applications.
-/

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped BigOperators

namespace WishartVerification

structure PositiveTemperatePrimitive (p : ℕ) where
  val : SymmetricMatrix p → ℝ
  growth : val.HasTemperateGrowth
  lower : ∃ δ : ℝ, 0 < δ ∧ ∀ X, δ ≤ val X

instance {p : ℕ} : CoeFun (PositiveTemperatePrimitive p) (fun _ => SymmetricMatrix p → ℝ) :=
  ⟨PositiveTemperatePrimitive.val⟩

namespace PositiveTemperatePrimitive

variable {p : ℕ} (Q : PositiveTemperatePrimitive p)

theorem pos (X : SymmetricMatrix p) : 0 < Q X := by
  obtain ⟨δ, hδ, hbound⟩ := Q.lower
  exact hδ.trans_le (hbound X)

theorem power_growth (a : ℝ) : (fun X => Q X ^ a).HasTemperateGrowth := by
  obtain ⟨δ, hδ, hbound⟩ := Q.lower
  exact hasTemperateGrowth_rpow_of_pos_lower Q.growth hδ hbound a

theorem differentiable (X : SymmetricMatrix p) : DifferentiableAt ℝ Q X :=
  Q.growth.1.differentiable (by simp) X

theorem directional_differentiable (X H : SymmetricMatrix p) :
    DifferentiableAt ℝ (fun Y => fderiv ℝ Q Y H) X := by
  have h : (fun Y : SymmetricMatrix p => fderiv ℝ Q Y H).HasTemperateGrowth := by
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply] using
      (ContinuousLinearMap.apply ℝ ℝ H).hasTemperateGrowth.comp
        (hasTemperateGrowth_fderiv Q.growth)
  exact h.1.differentiable (by simp) X

theorem log_differentiable (X : SymmetricMatrix p) :
    DifferentiableAt ℝ (fun Y => Real.log (Q Y)) X :=
  (Q.differentiable X).log (Q.pos X).ne'

theorem log_directional_differentiable (X H : SymmetricMatrix p) :
    DifferentiableAt ℝ (fun Y => fderiv ℝ (fun Z => Real.log (Q Z)) Y H) X :=
  differentiableAt_directional_fderiv_log
    (Filter.Eventually.of_forall Q.differentiable)
    (Filter.Eventually.of_forall fun Y => (Q.pos Y).ne')
    (Q.directional_differentiable X) H

end PositiveTemperatePrimitive

variable {p : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]

def primitivePowerSum (L : ℝ) (Q : ι → PositiveTemperatePrimitive p)
    (a b : ι → ℝ) (X : SymmetricMatrix p) : ℝ :=
  ∑ j, Real.exp (L * b j) * Q j X ^ (L * a j)

def primitivePowerMean (L : ℝ) (Q : ι → PositiveTemperatePrimitive p)
    (a b : ι → ℝ) (X : SymmetricMatrix p) : ℝ :=
  (primitivePowerSum L Q a b X / Fintype.card ι) ^ (1 / L)

def primitiveAffineLog (L : ℝ) (Q : ι → PositiveTemperatePrimitive p)
    (a b : ι → ℝ) (j : ι) (X : SymmetricMatrix p) : ℝ :=
  (L * a j) * Real.log (Q j X) + L * b j

def primitiveMeanLog (L : ℝ) (Q : ι → PositiveTemperatePrimitive p)
    (a b : ι → ℝ) (X : SymmetricMatrix p) : ℝ :=
  (1 / L) * Real.log (exponentialSum (primitiveAffineLog L Q a b) X) +
    -(Real.log (Fintype.card ι) / L)

theorem primitivePowerSum_pos (L : ℝ) (Q : ι → PositiveTemperatePrimitive p)
    (a b : ι → ℝ) (X : SymmetricMatrix p) : 0 < primitivePowerSum L Q a b X :=
  Finset.sum_pos (fun j _ => mul_pos (Real.exp_pos _)
    (Real.rpow_pos_of_pos ((Q j).pos X) _)) Finset.univ_nonempty

theorem primitivePowerSum_growth (L : ℝ) (Q : ι → PositiveTemperatePrimitive p)
    (a b : ι → ℝ) : (primitivePowerSum L Q a b).HasTemperateGrowth :=
  Function.HasTemperateGrowth.sum fun j _ =>
    (Function.HasTemperateGrowth.const _).mul ((Q j).power_growth _)

theorem primitivePowerSum_lower {L : ℝ} (hL : 0 < L)
    (Q : ι → PositiveTemperatePrimitive p) (a b : ι → ℝ) (ha : ∀ j, 0 ≤ a j) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ X, δ ≤ primitivePowerSum L Q a b X := by
  classical
  let j : ι := Classical.choice inferInstance
  obtain ⟨δ, hδ, hbound⟩ := (Q j).lower
  refine ⟨Real.exp (L * b j) * δ ^ (L * a j),
    mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hδ _), fun X => ?_⟩
  have hsum : Real.exp (L * b j) * Q j X ^ (L * a j) ≤
      primitivePowerSum L Q a b X := by
    unfold primitivePowerSum
    exact Finset.single_le_sum (fun k _ => mul_nonneg (Real.exp_pos (L * b k)).le
      (Real.rpow_nonneg ((Q k).pos X).le (L * a k))) (Finset.mem_univ j)
  exact (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hδ.le (hbound X) (mul_nonneg hL.le (ha j)))
    (Real.exp_pos _).le).trans hsum

set_option backward.isDefEq.respectTransparency false in
theorem primitivePowerMean_growth {L : ℝ} (hL : 0 < L)
    (Q : ι → PositiveTemperatePrimitive p) (a b : ι → ℝ) (ha : ∀ j, 0 ≤ a j) :
    (primitivePowerMean L Q a b).HasTemperateGrowth := by
  obtain ⟨δ, hδ, hbound⟩ := primitivePowerSum_lower hL Q a b ha
  have hc : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hg : (fun X => primitivePowerSum L Q a b X / Fintype.card ι).HasTemperateGrowth := by
    have hmul := (primitivePowerSum_growth L Q a b).mul
      (Function.HasTemperateGrowth.const (Fintype.card ι : ℝ)⁻¹)
    have heq : (primitivePowerSum L Q a b * fun _ => (Fintype.card ι : ℝ)⁻¹) =
        fun X => primitivePowerSum L Q a b X * (Fintype.card ι : ℝ)⁻¹ := rfl
    rw [heq] at hmul
    simpa only [div_eq_mul_inv] using hmul
  exact hasTemperateGrowth_rpow_of_pos_lower hg (div_pos hδ hc)
    (fun X => div_le_div_of_nonneg_right (hbound X) hc.le) (1 / L)

theorem primitiveAffineLog_exp (L : ℝ) (Q : ι → PositiveTemperatePrimitive p)
    (a b : ι → ℝ) (j : ι) (X : SymmetricMatrix p) :
    Real.exp (primitiveAffineLog L Q a b j X) =
      Real.exp (L * b j) * Q j X ^ (L * a j) := by
  rw [primitiveAffineLog, Real.exp_add, Real.rpow_def_of_pos ((Q j).pos X)]
  rw [mul_comm (L * a j), mul_comm]

theorem primitivePowerMean_eq_exp (L : ℝ) (Q : ι → PositiveTemperatePrimitive p)
    (a b : ι → ℝ) (X : SymmetricMatrix p) :
    primitivePowerMean L Q a b X = Real.exp (primitiveMeanLog L Q a b X) := by
  have hsum : primitivePowerSum L Q a b X =
      exponentialSum (primitiveAffineLog L Q a b) X := by
    unfold primitivePowerSum exponentialSum
    simp only [primitiveAffineLog_exp]
  have hc : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  rw [primitivePowerMean, hsum, Real.rpow_def_of_pos
    (div_pos (exponentialSum_pos _ X) hc),
    Real.log_div (exponentialSum_pos _ X).ne' hc.ne', primitiveMeanLog]
  congr 1
  ring

theorem primitiveAffineLog_differentiable_near (L : ℝ)
    (Q : ι → PositiveTemperatePrimitive p) (a b : ι → ℝ) (X : SymmetricMatrix p) :
    ∀ᶠ Y in 𝓝 X, ∀ j, DifferentiableAt ℝ (primitiveAffineLog L Q a b j) Y :=
  Filter.Eventually.of_forall fun Y j =>
    (((Q j).log_differentiable Y).const_mul _).add_const _

theorem primitiveAffineLog_directional_differentiable (L : ℝ)
    (Q : ι → PositiveTemperatePrimitive p) (a b : ι → ℝ)
    (X : SymmetricMatrix p) (j : ι) (H : SymmetricMatrix p) :
    DifferentiableAt ℝ (fun Y => fderiv ℝ (primitiveAffineLog L Q a b j) Y H) X :=
  differentiableAt_directional_fderiv_affine
    (Filter.Eventually.of_forall (Q j).log_differentiable)
    ((Q j).log_directional_differentiable X) (L * a j) (L * b j) H

theorem primitiveMeanLog_differentiable_near (L : ℝ)
    (Q : ι → PositiveTemperatePrimitive p) (a b : ι → ℝ) (X : SymmetricMatrix p) :
    ∀ᶠ Y in 𝓝 X, DifferentiableAt ℝ (primitiveMeanLog L Q a b) Y := by
  filter_upwards [logSumExp_differentiable_near (primitiveAffineLog L Q a b)
    (primitiveAffineLog_differentiable_near L Q a b X)] with Y hY
  exact (hY.const_mul (1 / L)).add_const _

theorem primitiveMeanLog_directional_differentiable (L : ℝ)
    (Q : ι → PositiveTemperatePrimitive p) (a b : ι → ℝ)
    (X H : SymmetricMatrix p) :
    DifferentiableAt ℝ (fun Y => fderiv ℝ (primitiveMeanLog L Q a b) Y H) X :=
  differentiableAt_directional_fderiv_affine
    (logSumExp_differentiable_near (primitiveAffineLog L Q a b)
      (primitiveAffineLog_differentiable_near L Q a b X))
    (logSumExp_direction_differentiable (primitiveAffineLog L Q a b)
      (primitiveAffineLog_differentiable_near L Q a b X)
      (primitiveAffineLog_directional_differentiable L Q a b X))
    (1 / L) (-(Real.log (Fintype.card ι) / L)) H

theorem primitiveMeanLog_generator_nonneg {L N : ℝ} (hL : 0 < L)
    (Q : ι → PositiveTemperatePrimitive p) (a b : ι → ℝ) (ha : ∀ j, 0 ≤ a j)
    {X : SymmetricMatrix p} (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    (v : EuclideanSpace ℝ (Fin p))
    (hQ : ∀ j, 0 ≤ symmetricDirectionalGenerator N v (fun Y => Real.log (Q j Y)) X) :
    0 ≤ symmetricDirectionalGenerator N v (primitiveMeanLog L Q a b) X := by
  let g := primitiveAffineLog L Q a b
  have hg := primitiveAffineLog_differentiable_near L Q a b X
  have hD := primitiveAffineLog_directional_differentiable L Q a b X
  have hgpos (j : ι) : 0 ≤ symmetricDirectionalGenerator N v (g j) X := by
    change 0 ≤ symmetricDirectionalGenerator N v
      (fun Y => (L * a j) * Real.log (Q j Y) + L * b j) X
    rw [symmetricDirectionalGenerator_affine
      (Filter.Eventually.of_forall (Q j).log_differentiable)
      ((Q j).log_directional_differentiable X)]
    exact mul_nonneg (mul_nonneg hL.le (ha j)) (hQ j)
  unfold primitiveMeanLog
  rw [symmetricDirectionalGenerator_affine
    (logSumExp_differentiable_near g hg) (logSumExp_direction_differentiable g hg hD)]
  exact mul_nonneg (one_div_nonneg.mpr hL.le)
    (symmetricDirectionalGenerator_logSumExp_nonneg g hX hg hD N v hgpos)

section Products

variable {κ : Type*} [Fintype κ]

def primitivePowerMeanProduct (L : ℝ) (Q : κ → ι → PositiveTemperatePrimitive p)
    (a b : κ → ι → ℝ) (X : SymmetricMatrix p) : ℝ :=
  ∏ i, primitivePowerMean L (Q i) (a i) (b i) X

def primitiveMaximumProduct (Q : κ → ι → PositiveTemperatePrimitive p)
    (a b : κ → ι → ℝ) (X : SymmetricMatrix p) : ℝ :=
  ∏ i, finiteMaximum (fun j => Real.exp (b i j) * Q i j X ^ (a i j))

theorem primitivePowerMeanProduct_growth {L : ℝ} (hL : 0 < L)
    (Q : κ → ι → PositiveTemperatePrimitive p) (a b : κ → ι → ℝ)
    (ha : ∀ i j, 0 ≤ a i j) : (primitivePowerMeanProduct L Q a b).HasTemperateGrowth :=
  hasTemperateGrowth_finset_prod Finset.univ _ fun i _ =>
    primitivePowerMean_growth hL (Q i) (a i) (b i) (ha i)

theorem primitivePowerMeanProduct_generator_nonneg {L N : ℝ} (hL : 0 < L)
    (Q : κ → ι → PositiveTemperatePrimitive p) (a b : κ → ι → ℝ)
    (ha : ∀ i j, 0 ≤ a i j)
    {X : SymmetricMatrix p} (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    (v : EuclideanSpace ℝ (Fin p))
    (hQ : ∀ i j, 0 ≤ symmetricDirectionalGenerator N v (fun Y => Real.log (Q i j Y)) X) :
    0 ≤ symmetricRadialGenerator N v (primitivePowerMeanProduct L Q a b) X := by
  let g : κ → SymmetricMatrix p → ℝ := fun i => primitiveMeanLog L (Q i) (a i) (b i)
  have hg : ∀ᶠ Y in 𝓝 X, ∀ i, DifferentiableAt ℝ (g i) Y :=
    Filter.eventually_all.mpr fun i => primitiveMeanLog_differentiable_near L (Q i) (a i) (b i) X
  have hD (i : κ) (H : SymmetricMatrix p) :
      DifferentiableAt ℝ (fun Y => fderiv ℝ (g i) Y H) X :=
    primitiveMeanLog_directional_differentiable L (Q i) (a i) (b i) X H
  have hsumnear : ∀ᶠ Y in 𝓝 X, DifferentiableAt ℝ (fun Z => ∑ i, g i Z) Y := by
    filter_upwards [hg] with Y hY
    exact DifferentiableAt.fun_sum fun i _ => hY i
  have hsumD (H : SymmetricMatrix p) :
      DifferentiableAt ℝ (fun Y => fderiv ℝ (fun Z => ∑ i, g i Z) Y H) X := by
    have heq : (fun Y => fderiv ℝ (fun Z => ∑ i, g i Z) Y H) =ᶠ[𝓝 X]
        (fun Y => ∑ i, fderiv ℝ (g i) Y H) := by
      filter_upwards [hg] with Y hY
      simpa only [one_mul] using
        fderiv_linear_combination_apply (fun _ : κ => (1 : ℝ)) g hY H
    exact heq.differentiableAt_iff.mpr (DifferentiableAt.fun_sum fun i _ => hD i H)
  have heq : primitivePowerMeanProduct L Q a b = fun Y => Real.exp (∑ i, g i Y) := by
    funext Y
    simp only [primitivePowerMeanProduct, primitivePowerMean_eq_exp, Real.exp_sum, g]
  rw [symmetricRadialGenerator_eq_directional (primitivePowerMeanProduct_growth hL Q a b ha),
    heq, symmetricDirectionalGenerator_exp hsumnear hsumD]
  apply mul_nonneg (Real.exp_pos _).le
  apply add_nonneg _ (symmetricCarreDuChamp_nonneg _ hX v)
  have hsum := symmetricDirectionalGenerator_linear_combination
    (fun _ : κ => (1 : ℝ)) g hg hD N v
  simp only [one_mul] at hsum
  rw [hsum]
  exact Finset.sum_nonneg fun i _ => primitiveMeanLog_generator_nonneg hL
    (Q i) (a i) (b i) (ha i) hX v (hQ i)

theorem primitivePowerMean_eq_finitePowerMean (L : ℝ)
    (Q : ι → PositiveTemperatePrimitive p) (a b : ι → ℝ) (X : SymmetricMatrix p) :
    primitivePowerMean L Q a b X =
      finitePowerMean L (fun j => Real.exp (b j) * Q j X ^ (a j)) := by
  unfold primitivePowerMean primitivePowerSum finitePowerMean
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  exact (monomial_power_eq (Q j X) ((Q j).pos X).le (a j) (b j) L).symm

theorem primitivePowerMeanProduct_integral_tendsto
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (Q : κ → ι → PositiveTemperatePrimitive p) (a b : κ → ι → ℝ)
    (Z : Ω → SymmetricMatrix p)
    (hmom : ∀ i j, HasAllFiniteMoments (fun z => Real.exp (b i j) * Q i j (Z z) ^ (a i j)) μ) :
    Tendsto (fun n : ℕ => ∫ z, primitivePowerMeanProduct ((n : ℝ) + 1) Q a b (Z z) ∂μ) atTop
      (𝓝 (∫ z, primitiveMaximumProduct Q a b (Z z) ∂μ)) := by
  have hpos : ∀ᵐ z ∂μ, ∀ i j, 0 ≤ Real.exp (b i j) * Q i j (Z z) ^ (a i j) :=
    Filter.Eventually.of_forall fun z i j =>
      mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg ((Q i j).pos (Z z)).le _)
  simpa only [primitivePowerMeanProduct, primitivePowerMean_eq_finitePowerMean,
    primitiveMaximumProduct] using
    powerMeanProduct_integral_tendsto (fun i j z => Real.exp (b i j) * Q i j (Z z) ^ (a i j)) hmom hpos

end Products

end WishartVerification

namespace Wishart

open WishartVerification

theorem monotoneOn_scalarRadial_primitiveMaximumProduct
    {r : ℕ} {N : ℝ} (hN : (r : ℝ) < N)
    {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (Q : κ → ι → PositiveTemperatePrimitive (1 + r)) (a b : κ → ι → ℝ)
    (ha : ∀ i j, 0 ≤ a i j)
    (hQ : ∀ X : SymmetricMatrix (1 + r),
      (X : Matrix (Fin (1 + r)) (Fin (1 + r)) ℝ).PosSemidef → ∀ i j,
      0 ≤ symmetricDirectionalGenerator N (scalarTransverseAxis r)
        (fun Y => Real.log (Q i j Y)) X) :
    MonotoneOn (fun t : ℝ => ∫ z : ScalarRegressionNoise r,
      primitiveMaximumProduct Q a b (scalarRadialMatrix (Real.sqrt t) z)
        ∂scalarRegressionNoiseMeasure N r) (Set.Ici 0) := by
  letI := isProbabilityMeasure_scalarRegressionNoiseMeasure hN
  have hmono (n : ℕ) := monotoneOn_scalarRadialProfile_of_generator_nonneg hN
    (primitivePowerMeanProduct_growth (by positivity : 0 < (n : ℝ) + 1) Q a b ha)
    (fun X hX => primitivePowerMeanProduct_generator_nonneg (by positivity)
      Q a b ha hX (scalarTransverseAxis r) (hQ X hX))
  have hlim (s : ℝ) := primitivePowerMeanProduct_integral_tendsto Q a b (scalarRadialMatrix s)
    (fun i j => show HasAllFiniteMoments
      (fun z => Real.exp (b i j) * Q i j (scalarRadialMatrix s z) ^ (a i j))
        (scalarRegressionNoiseMeasure N r) from by
      intro u hu
      apply memLp_temperate_of_allNormMoments (allFiniteNormMoments_scalarRegressionNoise hN) _ hu
      exact (Function.HasTemperateGrowth.const _).mul
        (((Q i j).power_growth _).comp ((hasTemperateGrowth_scalarRadialMatrix r).comp
          (hasTemperateGrowth_prodMk (Function.HasTemperateGrowth.const s)
            Function.HasTemperateGrowth.id))))
  intro s hs t ht hst
  exact le_of_tendsto_of_tendsto (hlim (Real.sqrt s)) (hlim (Real.sqrt t))
    (Filter.Eventually.of_forall fun n => hmono n hs ht hst)

end Wishart
end
end CanonicalSource65

section CanonicalSource66
/- Source: Wishart/TraceAffineGenerator.lean -/



/-!
# Genuine derivatives and radial generator of positive affine trace forms

The logarithmic generator is nonnegative for N≥2, independently of the
compression rank. This is equation (14), stated with the actual Fréchet
derivatives used by the radial expectation theorem.
-/

noncomputable section

open Matrix Filter Topology
open scoped MatrixOrder InnerProductSpace RealInnerProductSpace

namespace WishartVerification

variable {p : ℕ}

def traceFunctional (D : SymmetricMatrix p) : SymmetricMatrix p →L[ℝ] ℝ :=
  InnerProductSpace.toDual ℝ (SymmetricMatrix p) D

@[simp] theorem traceFunctional_apply (D X : SymmetricMatrix p) :
    traceFunctional D X = ⟪D, X⟫_ℝ := InnerProductSpace.toDual_apply_apply

def traceAffine (ε : ℝ) (A D : SymmetricMatrix p) (X : SymmetricMatrix p) : ℝ :=
  ε + ⟪D, A + X⟫_ℝ

def traceAffineLog (ε : ℝ) (A D : SymmetricMatrix p) (X : SymmetricMatrix p) : ℝ :=
  Real.log (traceAffine ε A D X)

theorem traceAffine_eq (ε : ℝ) (A D : SymmetricMatrix p) :
    traceAffine ε A D = fun X => (ε + ⟪D, A⟫_ℝ) + traceFunctional D X := by
  funext X
  simp only [traceAffine, inner_add_right, traceFunctional_apply, add_assoc]

theorem hasTemperateGrowth_traceAffine (ε : ℝ) (A D : SymmetricMatrix p) :
    (traceAffine ε A D).HasTemperateGrowth := by
  rw [traceAffine_eq]
  exact (Function.HasTemperateGrowth.const _).add (traceFunctional D).hasTemperateGrowth

theorem hasFDerivAt_traceAffine (ε : ℝ) (A D X : SymmetricMatrix p) :
    HasFDerivAt (traceAffine ε A D) (traceFunctional D) X := by
  rw [traceAffine_eq]
  exact (traceFunctional D).hasFDerivAt.const_add _

theorem fderiv_traceAffine (ε : ℝ) (A D X : SymmetricMatrix p) :
    fderiv ℝ (traceAffine ε A D) X = traceFunctional D :=
  (hasFDerivAt_traceAffine ε A D X).fderiv

theorem traceAffine_direction_differentiable (ε : ℝ) (A D X H : SymmetricMatrix p) :
    DifferentiableAt ℝ (fun Y => fderiv ℝ (traceAffine ε A D) Y H) X := by
  simp only [fderiv_traceAffine]
  exact differentiableAt_const _

theorem inner_rankOne (D : SymmetricMatrix p) (v : EuclideanSpace ℝ (Fin p)) :
    ⟪D, rankOneSymmetric v⟫_ℝ =
      (fun i => v i) ⬝ᵥ ((D : Matrix (Fin p) (Fin p) ℝ) *ᵥ (fun i => v i)) := by
  rw [selfAdjoint.inner_eq_trace_mul, coe_rankOneSymmetric,
    Matrix.trace_mul_comm, trace_mul_rankOne]

theorem inner_symmetricRankDirection (D : SymmetricMatrix p)
    (v : EuclideanSpace ℝ (Fin p)) (i : Fin p) :
    ⟪D, symmetricRankDirection v (coordinateVector i)⟫_ℝ =
      2 * ((D : Matrix (Fin p) (Fin p) ℝ) *ᵥ (fun j => v j)) i := by
  rw [selfAdjoint.inner_eq_trace_mul, coe_symmetricRankDirection,
    Matrix.trace_mul_comm]
  change Matrix.trace ((D : Matrix (Fin p) (Fin p) ℝ) *
    symRankOne (fun j => v j) (fun j => coordinateVector i j)) = _
  rw [trace_mul_symRankOne
    (Matrix.isHermitian_iff_isSymm.mp (selfAdjoint.isHermitian_coe D))]
  simp [coordinateVector_apply, dotProduct]

theorem symmetricDirectionalGenerator_traceAffine (ε : ℝ) (A D X : SymmetricMatrix p)
    (N : ℝ) (v : EuclideanSpace ℝ (Fin p)) :
    symmetricDirectionalGenerator N v (traceAffine ε A D) X =
      2 * N * ((fun i => v i) ⬝ᵥ
        ((D : Matrix (Fin p) (Fin p) ℝ) *ᵥ (fun i => v i))) := by
  simp only [symmetricDirectionalGenerator, fderiv_traceAffine, traceFunctional_apply,
    fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.zero_apply, mul_zero, Finset.sum_const_zero,
    add_zero, inner_rankOne]

theorem symmetricCarreDuChamp_traceAffine (ε : ℝ) (A D X : SymmetricMatrix p)
    (v : EuclideanSpace ℝ (Fin p)) :
    symmetricCarreDuChamp (traceAffine ε A D) X v =
      4 * (((D : Matrix (Fin p) (Fin p) ℝ) *ᵥ (fun i => v i)) ⬝ᵥ
        ((X : Matrix (Fin p) (Fin p) ℝ) *ᵥ
          ((D : Matrix (Fin p) (Fin p) ℝ) *ᵥ (fun i => v i)))) := by
  have hquad (w : Fin p → ℝ) :
      (∑ i, ∑ j, (X : Matrix (Fin p) (Fin p) ℝ) i j * (2 * w i) * (2 * w j)) =
        4 * (w ⬝ᵥ ((X : Matrix (Fin p) (Fin p) ℝ) *ᵥ w)) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simpa only [symmetricCarreDuChamp, fderiv_traceAffine, traceFunctional_apply,
    inner_symmetricRankDirection] using
    hquad ((D : Matrix (Fin p) (Fin p) ℝ) *ᵥ (fun i => v i))

theorem traceAffine_pos {ε : ℝ} (hε : 0 < ε) {A D X : SymmetricMatrix p}
    (hA : (A : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    (hD : (D : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    0 < traceAffine ε A D X := by
  unfold traceAffine
  apply add_pos_of_pos_of_nonneg hε
  rw [selfAdjoint.inner_eq_trace_mul, Matrix.trace_mul_comm]
  exact trace_mul_nonneg_of_posSemidef hD (hA.add hX)

theorem traceAffineLog_differentiable_near (ε : ℝ) (A D : SymmetricMatrix p)
    {X : SymmetricMatrix p} (hQ : traceAffine ε A D X ≠ 0) :
    ∀ᶠ Y in 𝓝 X, DifferentiableAt ℝ (traceAffineLog ε A D) Y := by
  filter_upwards [(hasTemperateGrowth_traceAffine ε A D).1.continuous.continuousAt.eventually_ne hQ]
    with Y hY
  exact (hasFDerivAt_traceAffine ε A D Y).differentiableAt.log hY

theorem symmetricDirectionalGenerator_traceAffineLog (ε : ℝ) (A D : SymmetricMatrix p)
    {X : SymmetricMatrix p} (hQ : traceAffine ε A D X ≠ 0)
    (N : ℝ) (v : EuclideanSpace ℝ (Fin p)) :
    symmetricDirectionalGenerator N v (traceAffineLog ε A D) X =
      2 * N * ((fun i => v i) ⬝ᵥ
        ((D : Matrix (Fin p) (Fin p) ℝ) *ᵥ (fun i => v i))) / traceAffine ε A D X -
      4 * (((D : Matrix (Fin p) (Fin p) ℝ) *ᵥ (fun i => v i)) ⬝ᵥ
        ((X : Matrix (Fin p) (Fin p) ℝ) *ᵥ
          ((D : Matrix (Fin p) (Fin p) ℝ) *ᵥ (fun i => v i)))) /
        traceAffine ε A D X ^ 2 := by
  have hg : ∀ᶠ Y in 𝓝 X, DifferentiableAt ℝ (traceAffine ε A D) Y :=
    Filter.Eventually.of_forall fun Y => (hasFDerivAt_traceAffine ε A D Y).differentiableAt
  have hlog : ∀ᶠ Y in 𝓝 X, DifferentiableAt ℝ Real.log (traceAffine ε A D Y) := by
    filter_upwards [(hasTemperateGrowth_traceAffine ε A D).1.continuous.continuousAt.eventually_ne hQ]
      with Y hY
    exact Real.differentiableAt_log hY
  have hlog' : DifferentiableAt ℝ (deriv Real.log) (traceAffine ε A D X) := by
    rw [Real.deriv_log']
    exact (hasDerivAt_inv hQ).differentiableAt
  change symmetricDirectionalGenerator N v (fun Y => Real.log (traceAffine ε A D Y)) X = _
  rw [symmetricDirectionalGenerator_scalar_comp hg hlog hlog'
    (traceAffine_direction_differentiable ε A D X), Real.deriv_log,
    Real.deriv_log', deriv_inv, symmetricDirectionalGenerator_traceAffine,
    symmetricCarreDuChamp_traceAffine]
  ring

/-- Equation (14), with the exact dimension-free threshold. -/
theorem symmetricDirectionalGenerator_traceAffineLog_nonneg {ε N : ℝ}
    (hε : 0 < ε) (hN : 2 ≤ N) {A D X : SymmetricMatrix p}
    (hA : (A : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    (hD : (D : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    (v : EuclideanSpace ℝ (Fin p)) :
    0 ≤ symmetricDirectionalGenerator N v (traceAffineLog ε A D) X := by
  have hQ := traceAffine_pos hε hA hD hX
  rw [symmetricDirectionalGenerator_traceAffineLog ε A D hQ.ne']
  have hbound := positive_affine_log_generator_lower_bound hD hX hA hε N (fun i => v i)
  have heq : traceAffine ε A D X =
      ε + ((D : Matrix (Fin p) (Fin p) ℝ) *
        ((A : Matrix (Fin p) (Fin p) ℝ) + (X : Matrix (Fin p) (Fin p) ℝ))).trace := by
    rw [traceAffine, selfAdjoint.inner_eq_trace_mul, Matrix.trace_mul_comm]
    rfl
  rw [← heq] at hbound
  refine le_trans ?_ hbound
  apply div_nonneg _ hQ.le
  apply mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hN))
  simpa only [star_trivial] using hD.dotProduct_mulVec_nonneg (fun i => v i)

end WishartVerification
end
end CanonicalSource66

section CanonicalSource67
/- Source: Wishart/TracePrimitiveMeans.lean -/



/-!
# Positive trace supports and the dimension-free radial threshold

Each primitive is a globally smooth extension of ε+c+tr(DX), for c≥0
and D positive semidefinite. The extension agrees locally on the entire
positive cone with that exact affine trace. Its logarithmic generator is
therefore nonnegative at N≥2. Passing first through power means and then
ε↓0 yields the finite-support comparison used for convex spectral gauges.
-/

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped BigOperators InnerProductSpace RealInnerProductSpace

namespace WishartVerification

variable {p : ℕ}

def positiveTracePrimitive (ε : ℝ) (hε : 0 < ε) (c : ℝ) (D : SymmetricMatrix p) :
    PositiveTemperatePrimitive p where
  val X := smoothPositivePower (ε / 2) 1 (traceAffine (ε + c) 0 D X)
  growth := (hasTemperateGrowth_smoothPositivePower (half_pos hε) 1).comp
    (hasTemperateGrowth_traceAffine (ε + c) 0 D)
  lower := ⟨ε / 2 / 2, by positivity, fun X => by
    simpa only [Real.rpow_one] using
      smoothPositivePower_lower (half_pos hε) (show (0 : ℝ) ≤ 1 by norm_num)
        (traceAffine (ε + c) 0 D X)⟩

theorem inner_nonneg_of_posSemidef {D X : SymmetricMatrix p}
    (hD : (D : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef) : 0 ≤ ⟪D, X⟫_ℝ := by
  rw [selfAdjoint.inner_eq_trace_mul]
  exact trace_mul_nonneg_of_posSemidef hX hD

theorem positiveTracePrimitive_eventually_eq {ε c : ℝ} (hε : 0 < ε) (hc : 0 ≤ c)
    {D X : SymmetricMatrix p}
    (hD : (D : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    (positiveTracePrimitive ε hε c D : SymmetricMatrix p → ℝ) =ᶠ[𝓝 X]
      traceAffine (ε + c) 0 D := by
  have hval : ε / 2 < traceAffine (ε + c) 0 D X := by
    have hinner := inner_nonneg_of_posSemidef hD hX
    simp only [traceAffine, zero_add]
    linarith
  filter_upwards [(hasTemperateGrowth_traceAffine (ε + c) 0 D).1.continuous.continuousAt.eventually
    (Ioi_mem_nhds hval)] with Y hY
  change smoothPositivePower (ε / 2) 1 (traceAffine (ε + c) 0 D Y) = _
  rw [smoothPositivePower_eq (half_pos hε) hY.le, Real.rpow_one]

theorem positiveTracePrimitive_eq {ε c : ℝ} (hε : 0 < ε) (hc : 0 ≤ c)
    {D X : SymmetricMatrix p}
    (hD : (D : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    positiveTracePrimitive ε hε c D X = ε + c + ⟪D, X⟫_ℝ := by
  have h := (positiveTracePrimitive_eventually_eq hε hc hD hX).eq_of_nhds
  simpa only [traceAffine, zero_add] using h

theorem positiveTracePrimitive_log_generator_nonneg {ε c N : ℝ}
    (hε : 0 < ε) (hc : 0 ≤ c) (hN : 2 ≤ N) {D X : SymmetricMatrix p}
    (hD : (D : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    (v : EuclideanSpace ℝ (Fin p)) :
    0 ≤ symmetricDirectionalGenerator N v
      (fun Y => Real.log (positiveTracePrimitive ε hε c D Y)) X := by
  have heq : (fun Y => Real.log (positiveTracePrimitive ε hε c D Y)) =ᶠ[𝓝 X]
      traceAffineLog (ε + c) 0 D := by
    filter_upwards [positiveTracePrimitive_eventually_eq hε hc hD hX] with Y hY
    exact congrArg Real.log hY
  rw [symmetricDirectionalGenerator_congr heq]
  exact symmetricDirectionalGenerator_traceAffineLog_nonneg (add_pos_of_pos_of_nonneg hε hc)
    hN Matrix.PosSemidef.zero hD hX v

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]

def traceMaximumProduct (ε : ℝ) (c a b : κ → ι → ℝ)
    (D : κ → ι → SymmetricMatrix p) (X : SymmetricMatrix p) : ℝ :=
  ∏ i, finiteMaximum (fun j => Real.exp (b i j) * (ε + c i j + ⟪D i j, X⟫_ℝ) ^ (a i j))

theorem primitiveMaximumProduct_trace_eq {ε : ℝ} (hε : 0 < ε)
    (c a b : κ → ι → ℝ) (D : κ → ι → SymmetricMatrix p)
    (hc : ∀ i j, 0 ≤ c i j)
    (hD : ∀ i j, (D i j : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    {X : SymmetricMatrix p} (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    primitiveMaximumProduct (fun i j => positiveTracePrimitive ε hε (c i j) (D i j)) a b X =
      traceMaximumProduct ε c a b D X := by
  unfold primitiveMaximumProduct traceMaximumProduct
  congr 1
  funext i
  congr 1
  funext j
  rw [positiveTracePrimitive_eq hε (hc i j) (hD i j) hX]

theorem allFiniteMoments_traceMaximumProduct
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsFiniteMeasure μ]
    (hμ : HasAllFiniteMoments (fun z : E => ‖z‖) μ)
    {Z : E → SymmetricMatrix p} (hZ : Z.HasTemperateGrowth)
    (ε : ℝ) (c a b : κ → ι → ℝ) (D : κ → ι → SymmetricMatrix p)
    (ha : ∀ i j, 0 ≤ a i j) :
    HasAllFiniteMoments (fun z => traceMaximumProduct ε c a b D (Z z)) μ := by
  apply HasAllFiniteMoments.finset_prod Finset.univ
  intro i _
  apply hasAllFiniteMoments_finiteMaximum
  intro j
  have htrace : HasAllFiniteMoments (fun z => ε + c i j + ⟪D i j, Z z⟫_ℝ) μ := by
    intro u hu
    apply memLp_temperate_of_allNormMoments hμ _ hu
    exact (Function.HasTemperateGrowth.const _).add
      ((traceFunctional (D i j)).hasTemperateGrowth.comp hZ)
  exact (htrace.rpow (ha i j)).const_mul (Real.exp (b i j))

theorem traceMaximumProduct_mono_epsilon (c a b : κ → ι → ℝ)
    (D : κ → ι → SymmetricMatrix p) (hc : ∀ i j, 0 ≤ c i j)
    (ha : ∀ i j, 0 ≤ a i j)
    (hD : ∀ i j, (D i j : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    {X : SymmetricMatrix p} (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    {ε δ : ℝ} (hε : 0 ≤ ε) (hεδ : ε ≤ δ) :
    traceMaximumProduct ε c a b D X ≤ traceMaximumProduct δ c a b D X := by
  apply Finset.prod_le_prod₀
  · intro i _
    apply finiteMaximum_nonneg
    intro j
    exact mul_nonneg (Real.exp_pos _).le
      (Real.rpow_nonneg (add_nonneg (add_nonneg hε (hc i j))
        (inner_nonneg_of_posSemidef (hD i j) hX)) _)
  · intro i _
    apply finiteMaximum_mono
    intro j
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    exact Real.rpow_le_rpow
      (add_nonneg (add_nonneg hε (hc i j)) (inner_nonneg_of_posSemidef (hD i j) hX))
      (by linarith) (ha i j)

theorem traceMaximumProduct_nonneg (ε : ℝ) (hε : 0 ≤ ε)
    (c a b : κ → ι → ℝ) (D : κ → ι → SymmetricMatrix p)
    (hc : ∀ i j, 0 ≤ c i j)
    (hD : ∀ i j, (D i j : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    {X : SymmetricMatrix p} (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    0 ≤ traceMaximumProduct ε c a b D X := by
  apply Finset.prod_nonneg
  intro i _
  apply finiteMaximum_nonneg
  intro j
  exact mul_nonneg (Real.exp_pos _).le
    (Real.rpow_nonneg (add_nonneg (add_nonneg hε (hc i j))
      (inner_nonneg_of_posSemidef (hD i j) hX)) _)

theorem traceMaximumProduct_continuous_epsilon (c a b : κ → ι → ℝ)
    (D : κ → ι → SymmetricMatrix p) (ha : ∀ i j, 0 ≤ a i j)
    (X : SymmetricMatrix p) : Continuous (fun ε => traceMaximumProduct ε c a b D X) := by
  apply continuous_finsetProd
  intro i _
  apply continuous_finiteMaximum
  intro j
  exact continuous_const.mul ((Real.continuous_rpow_const (ha i j)).comp
    ((continuous_id.add continuous_const).add continuous_const))

end WishartVerification

namespace Wishart

open WishartVerification

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]

theorem monotoneOn_scalarRadial_traceMaximumProduct_regularized
    {r : ℕ} {N ε : ℝ} (hN : (r : ℝ) < N) (hNtwo : 2 ≤ N) (hε : 0 < ε)
    (c a b : κ → ι → ℝ) (D : κ → ι → SymmetricMatrix (1 + r))
    (hc : ∀ i j, 0 ≤ c i j) (ha : ∀ i j, 0 ≤ a i j)
    (hD : ∀ i j, (D i j : Matrix (Fin (1 + r)) (Fin (1 + r)) ℝ).PosSemidef) :
    MonotoneOn (fun t : ℝ => ∫ z : ScalarRegressionNoise r,
      traceMaximumProduct ε c a b D (scalarRadialMatrix (Real.sqrt t) z)
        ∂scalarRegressionNoiseMeasure N r) (Set.Ici 0) := by
  have hmono := monotoneOn_scalarRadial_primitiveMaximumProduct hN
    (fun i j => positiveTracePrimitive ε hε (c i j) (D i j)) a b ha
    (fun X hX i j => positiveTracePrimitive_log_generator_nonneg hε (hc i j) hNtwo
      (hD i j) hX (scalarTransverseAxis r))
  have heq (t : ℝ) : (∫ z : ScalarRegressionNoise r,
      primitiveMaximumProduct (fun i j => positiveTracePrimitive ε hε (c i j) (D i j)) a b
        (scalarRadialMatrix (Real.sqrt t) z) ∂scalarRegressionNoiseMeasure N r) =
      ∫ z : ScalarRegressionNoise r, traceMaximumProduct ε c a b D
        (scalarRadialMatrix (Real.sqrt t) z) ∂scalarRegressionNoiseMeasure N r := by
    apply integral_congr_ae
    filter_upwards [ae_scalarRadialMatrix_posSemidef N (Real.sqrt t)] with z hz
    exact primitiveMaximumProduct_trace_eq hε c a b D hc hD hz
  simpa only [heq] using hmono

theorem scalar_traceMaximumProduct_integral_tendsto
    {r : ℕ} {N : ℝ} (hN : (r : ℝ) < N)
    (c a b : κ → ι → ℝ) (D : κ → ι → SymmetricMatrix (1 + r))
    (hc : ∀ i j, 0 ≤ c i j) (ha : ∀ i j, 0 ≤ a i j)
    (hD : ∀ i j, (D i j : Matrix (Fin (1 + r)) (Fin (1 + r)) ℝ).PosSemidef)
    (s : ℝ) :
    Tendsto (fun n => ∫ z : ScalarRegressionNoise r,
      traceMaximumProduct (determinantRegularization n) c a b D (scalarRadialMatrix s z)
        ∂scalarRegressionNoiseMeasure N r) atTop
      (𝓝 (∫ z : ScalarRegressionNoise r, traceMaximumProduct 0 c a b D (scalarRadialMatrix s z)
        ∂scalarRegressionNoiseMeasure N r)) := by
  letI := isProbabilityMeasure_scalarRegressionNoiseMeasure hN
  have hZ := (hasTemperateGrowth_scalarRadialMatrix r).comp
    (hasTemperateGrowth_prodMk (Function.HasTemperateGrowth.const s) Function.HasTemperateGrowth.id)
  have hm (ε : ℝ) := allFiniteMoments_traceMaximumProduct
    (allFiniteNormMoments_scalarRegressionNoise hN) hZ ε c a b D ha
  refine tendsto_integral_of_dominated_convergence
    (fun z => traceMaximumProduct 1 c a b D (scalarRadialMatrix s z))
    (fun n => (hm (determinantRegularization n)).integrable.aestronglyMeasurable)
    (hm 1).integrable ?_ ?_
  · intro n
    filter_upwards [ae_scalarRadialMatrix_posSemidef N s] with z hz
    rw [Real.norm_of_nonneg (traceMaximumProduct_nonneg _
      (determinantRegularization_pos n).le c a b D hc hD hz)]
    exact traceMaximumProduct_mono_epsilon c a b D hc ha hD hz
      (determinantRegularization_pos n).le (determinantRegularization_le_one n)
  · exact Filter.Eventually.of_forall fun z =>
      (traceMaximumProduct_continuous_epsilon c a b D ha (scalarRadialMatrix s z)).continuousAt.tendsto.comp
        tendsto_determinantRegularization

/-- The dimension-free N≥2 trace-support comparison, with the actual
real-shape residual law and no unproved generator premise. -/
theorem monotoneOn_scalarRadial_traceMaximumProduct
    {r : ℕ} {N : ℝ} (hN : (r : ℝ) < N) (hNtwo : 2 ≤ N)
    (c a b : κ → ι → ℝ) (D : κ → ι → SymmetricMatrix (1 + r))
    (hc : ∀ i j, 0 ≤ c i j) (ha : ∀ i j, 0 ≤ a i j)
    (hD : ∀ i j, (D i j : Matrix (Fin (1 + r)) (Fin (1 + r)) ℝ).PosSemidef) :
    MonotoneOn (fun t : ℝ => ∫ z : ScalarRegressionNoise r,
      traceMaximumProduct 0 c a b D (scalarRadialMatrix (Real.sqrt t) z)
        ∂scalarRegressionNoiseMeasure N r) (Set.Ici 0) := by
  intro s hs t ht hst
  exact le_of_tendsto_of_tendsto
    (scalar_traceMaximumProduct_integral_tendsto hN c a b D hc ha hD (Real.sqrt s))
    (scalar_traceMaximumProduct_integral_tendsto hN c a b D hc ha hD (Real.sqrt t))
    (Filter.Eventually.of_forall fun n =>
      monotoneOn_scalarRadial_traceMaximumProduct_regularized hN hNtwo
        (determinantRegularization_pos n) c a b D hc ha hD hs ht hst)

end Wishart
end
end CanonicalSource67

section CanonicalSource68
/- Source: Wishart/RegressionTestAssembly.lean -/



/-!
# Regression assembly for polynomially bounded positive-cone tests

This module separates the common measure-theoretic argument from the concrete
trace and compression-monomial comparisons. The two auxiliary premises are an
all-moments closure property and an actual scalar-regression integral comparison.
Applications prove both for their literal tests; neither is asserted as an axiom
or substituted for a principal theorem.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification
open scoped Matrix MatrixOrder Matrix.Norms.Operator

namespace WishartVerification

/-- Finite matrix entry moments suffice for every finite moment of this test.
Only PSD inputs are constrained, since all conditional sources have that support. -/
def MatrixTestAllMoments {p : ℕ} (F : SymmetricMatrix p → ℝ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : Ω → SymmetricMatrix p}, Measurable X →
    (∀ᵐ z ∂μ, (X z : Matrix (Fin p) (Fin p) ℝ).PosSemidef) →
    (∀ i j : Fin p, HasAllFiniteMoments
      (fun z => (X z : Matrix (Fin p) (Fin p) ℝ) i j) μ) →
    HasAllFiniteMoments (fun z => F (X z)) μ

theorem MatrixTestAllMoments.wishart {p : ℕ} {F : SymmetricMatrix p → ℝ}
    (hF : MatrixTestAllMoments F) (n : ℝ) (C : Matrix (Fin p) (Fin p) ℝ) :
    HasAllFiniteMoments F (nonsingularWishartMeasure n C) := by
  exact hF measurable_id
    ((ae_posDef_nonsingularWishartMeasure n C).mono fun X hX => hX.posSemidef)
    (fun i j => allFiniteMoments_wishart_entry (α := n) (Sigma := C) i j)

end WishartVerification

namespace Wishart

def ScalarRadialTestMonotone {p : ℕ} (N : ℝ) (r : ℕ)
    (F : SymmetricMatrix p → ℝ) : Prop :=
  ∀ B : SymmetricMatrix p, (B : Matrix (Fin p) (Fin p) ℝ).PosSemidef →
    ∀ (L : Matrix (Fin p) (Fin r) ℝ) (v : EuclideanSpace ℝ (Fin p)),
      MonotoneOn (fun t : ℝ => ∫ z : ScalarRegressionNoise r,
        F (B + linearRadialInput L v (Real.sqrt t) z)
          ∂scalarRegressionNoiseMeasure N r) (Set.Ici 0)

theorem monotoneOn_linearShiftedRows_test_coordinate
    {q m p : ℕ} {ν : ℝ} (hν : (m : ℝ) - 1 < ν)
    {F : SymmetricMatrix p → ℝ} (hFm : Measurable F)
    (hFM : MatrixTestAllMoments F) (hrad : ScalarRadialTestMonotone (ν + 1) m F)
    (L : Matrix (Fin p) (Fin m) ℝ)
    (v : Fin q → EuclideanSpace ℝ (Fin p)) (lam : Fin q → ℝ) (a : Fin q) :
    MonotoneOn (fun t : ℝ => ∫ x,
      F (linearShiftedRowsSym L v (Function.update lam a t) x)
        ∂gaussianResidualMeasure q 1 (nonsingularWishartMeasure ν 1)) (Set.Ici 0) := by
  letI := isProbabilityMeasure_nonsingularWishartMeasure
    (S := (1 : Matrix (Fin m) (Fin m) ℝ)) Matrix.PosDef.one hν
  cases q with
  | zero => exact Fin.elim0 a
  | succ q =>
    let μ := Measure.pi (fun _ : Fin q =>
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) 1)
    let ρ := scalarRegressionNoiseMeasure (ν + 1) m
    let B (z : Fin q → EuclideanSpace ℝ (Fin m)) :=
      rowBackground (v ∘ a.succAbove) (lam ∘ a.succAbove) (gaussianRowsLinearMap L z)
    let H (t : ℝ) (y : (Fin q → EuclideanSpace ℝ (Fin m)) × ScalarRegressionNoise m) :=
      F (B y.1 + linearRadialInput L (v a) (Real.sqrt t) y.2)
    have hsplit := measurePreserving_separateScalarRegressionRow (m := m) ν a
    have hHm (t : ℝ) : Measurable (H t) := by
      apply hFm.comp
      apply Measurable.add
      · exact ((measurable_rowBackground _ _).comp
          (measurable_gaussianRowsLinearMap L)).comp measurable_fst
      · exact (measurable_linearRadialInput L (v a) (Real.sqrt t)).comp measurable_snd
    have hHcomp (t : ℝ) : H t ∘ separateScalarRegressionRow a =
        (fun x => F (linearShiftedRowsSym L v (Function.update lam a t) x)) := by
      funext x
      dsimp only [H, B, Function.comp_apply]
      rw [linearShiftedRowsSym_separate]
    have hHi (t : ℝ) : Integrable (H t) (μ.prod ρ) := by
      rw [← hsplit.map_eq]
      apply (integrable_map_measure (hHm t).aestronglyMeasurable
        hsplit.measurable.aemeasurable).mpr
      rw [hHcomp]
      apply HasAllFiniteMoments.integrable
      apply hFM (measurable_linearShiftedRowsSym L v (Function.update lam a t))
      · filter_upwards [Measure.quasiMeasurePreserving_snd.ae
          (ae_posDef_nonsingularWishartMeasure ν (1 : Matrix (Fin m) (Fin m) ℝ))] with x hx
        exact linearShiftedRowsSym_posSemidef L v _ x hx.posSemidef
      · exact allFiniteMoments_linearShiftedRowsSym_entry 1
          (fun i j => allFiniteMoments_wishart_entry (α := ν)
            (Sigma := (1 : Matrix (Fin m) (Fin m) ℝ)) i j) L v _
    have heq (t : ℝ) :
        (∫ x, F (linearShiftedRowsSym L v (Function.update lam a t) x)
          ∂gaussianResidualMeasure (q + 1) 1 (nonsingularWishartMeasure ν 1)) =
        ∫ z, ∫ Y, H t (z, Y) ∂ρ ∂μ := by
      rw [← integral_prod _ (hHi t), ← hsplit.map_eq,
        integral_map hsplit.measurable.aemeasurable (hHm t).aestronglyMeasurable]
      exact congrArg (fun f => ∫ x, f x
        ∂gaussianResidualMeasure (q + 1) 1 (nonsingularWishartMeasure ν 1)) (hHcomp t).symm
    intro s hs t ht hst
    dsimp only
    rw [heq s, heq t]
    apply integral_mono_ae (hHi s).integral_prod_left (hHi t).integral_prod_left
    exact Filter.Eventually.of_forall fun z =>
      hrad (B z) (rowBackground_posSemidef _ _ _) L (v a) hs ht hst

theorem monotoneOn_linearShiftedRows_test
    {q m p : ℕ} {ν : ℝ} (hν : (m : ℝ) - 1 < ν)
    {F : SymmetricMatrix p → ℝ} (hFm : Measurable F)
    (hFM : MatrixTestAllMoments F) (hrad : ScalarRadialTestMonotone (ν + 1) m F)
    (L : Matrix (Fin p) (Fin m) ℝ) (v : Fin q → EuclideanSpace ℝ (Fin p)) :
    MonotoneOn (fun lam : Fin q → ℝ => ∫ x,
      F (linearShiftedRowsSym L v lam x)
        ∂gaussianResidualMeasure q 1 (nonsingularWishartMeasure ν 1))
      (Set.Ici (0 : Fin q → ℝ)) :=
  monotoneOn_nonnegative_pi_of_update _ fun lam a =>
    monotoneOn_linearShiftedRows_test_coordinate hν hFm hFM hrad L v lam a

theorem monotoneOn_fullSpectralConditionalMoment_test
    {q m : ℕ} {n : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (K : Matrix (Fin q) (Fin m) ℝ) (O : Matrix (Fin q) (Fin q) ℝ)
    {F : SymmetricMatrix (q + m) → ℝ} (hFm : Measurable F)
    (hFM : MatrixTestAllMoments F) (hrad : ScalarRadialTestMonotone (n - q + 1) m F) :
    MonotoneOn (fun lam => fullSpectralConditionalMoment n C K F lam O)
      (Set.Ici (0 : Fin q → ℝ)) := by
  have hν : (m : ℝ) - 1 < n - q := by
    push_cast at hn
    linarith
  intro lam hlam lam' hlam' hle
  dsimp only
  rw [fullSpectralConditionalMoment_standardNoise n hC K O lam hFm,
    fullSpectralConditionalMoment_standardNoise n hC K O lam' hFm]
  exact monotoneOn_linearShiftedRows_test hν hFm hFM hrad
    (regressionNoiseInjection q m * CFC.sqrt C) (fullSpectralRegressionDirections K O)
      hlam hlam' hle

set_option maxHeartbeats 1200000 in
@[fun_prop] theorem measurable_haarFullRegressionModel {q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (lam : Fin q → ℝ) :
    Measurable (fun y : Spectral.Orth q × RegressionNoise q m =>
      fullSpectralRegressionModel K ↑y.1 lam y.2) := by
  have hm : Measurable (fun O : Spectral.Orth q => fullSpectralRegressionMean K ↑O lam) :=
    (measurable_fullSpectralRegressionMean K).comp
      (measurable_const.prodMk measurable_subtype_coe)
  exact measurable_regressionGramWithMean_uncurry.comp
    ((hm.comp measurable_fst).prodMk
      ((measurable_regressionNoiseLinearMap (regressionNoiseInjection q m)).comp measurable_snd))

theorem integrable_haar_fullSpectralConditionalMoment_test
    {q m : ℕ} {n : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {F : SymmetricMatrix (q + m) → ℝ} (hFM : MatrixTestAllMoments F)
    (lam : Fin q → ℝ) :
    Integrable (fun O : Spectral.Orth q => fullSpectralConditionalMoment n C K F lam ↑O)
      (haarProb (Spectral.Orth q)) := by
  letI := isProbabilityMeasure_regressionNoiseMeasure hn hC
  have hp : ∀ᵐ y : Spectral.Orth q × RegressionNoise q m
      ∂(haarProb (Spectral.Orth q)).prod (regressionNoiseMeasure n q m C),
      (fullSpectralRegressionModel K ↑y.1 lam y.2 :
        Matrix (Fin (q + m)) (Fin (q + m)) ℝ).PosSemidef := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae
      (Measure.quasiMeasurePreserving_snd.ae
        (ae_posDef_nonsingularWishartMeasure (n - q) C))] with y hy
    exact fullSpectralRegressionModel_posSemidef K ↑y.1 lam y.2 hy.posSemidef
  exact (hFM (measurable_haarFullRegressionModel K lam) hp
    (allFiniteMoments_haarFullRegressionModel_entry hn hC K lam)).integrable.integral_prod_left

theorem monotoneOn_fullRegressionSpectralAverage_test
    {q m : ℕ} {n : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {F : SymmetricMatrix (q + m) → ℝ} (hFm : Measurable F)
    (hFM : MatrixTestAllMoments F) (hrad : ScalarRadialTestMonotone (n - q + 1) m F) :
    MonotoneOn (fullRegressionSpectralAverage n C K F) (Spectral.positiveChamber q) := by
  apply parameterAverageOn_monotoneOn
  · intro lam hlam
    exact integrable_haar_fullSpectralConditionalMoment_test hn hC K hFM lam
  · intro lam hlam lam' hlam' hle
    exact Filter.Eventually.of_forall fun O =>
      monotoneOn_fullSpectralConditionalMoment_test hn hC K ↑O hFm hFM hrad
        (fun i => (hlam.2 i).le) (fun i => (hlam'.2 i).le) hle

theorem fullRegressionSpectralAverage_test_nonneg
    {q m : ℕ} (n : ℝ) (C : Matrix (Fin m) (Fin m) ℝ)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {F : SymmetricMatrix (q + m) → ℝ}
    (hF0 : ∀ X : SymmetricMatrix (q + m),
      (X : Matrix (Fin (q + m)) (Fin (q + m)) ℝ).PosSemidef → 0 ≤ F X)
    (lam : Fin q → ℝ) : 0 ≤ fullRegressionSpectralAverage n C K F lam := by
  unfold fullRegressionSpectralAverage
  apply parameterAverageOn_nonneg
  intro lam' _ O
  apply integral_nonneg_of_ae
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae
    (ae_posDef_nonsingularWishartMeasure (n - q) C)] with x hx
  exact hF0 _ (fullSpectralRegressionModel_posSemidef K ↑O lam' x hx.posSemidef)

/-- Generic finite-moment selected split. The spectral expression is an exact
pointwise identity; the conditional monotonicity is an explicit auxiliary premise. -/
theorem regression_test_split_of_spectral_monotone
    {q m : ℕ} {n : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    {h : SymmetricMatrix q → ℝ} (hh : Measurable h)
    (hHM : HasAllFiniteMoments h (nonsingularWishartMeasure n 1))
    {f : (Fin q → ℝ) → ℝ} (hfm : Measurable f) (hf0 : ∀ lam, 0 ≤ f lam)
    (hfmono : MonotoneOn f (Spectral.positiveChamber q))
    (hspectral : ∀ lam ∈ Spectral.positiveChamber q, ∀ O : Spectral.Orth q,
      h (regressionSpectralMatrix (lam, O)) = f lam)
    {F : SymmetricMatrix (q + m) → ℝ} (hFm : Measurable F)
    (hFM : MatrixTestAllMoments F)
    (hF0 : ∀ X : SymmetricMatrix (q + m),
      (X : Matrix (Fin (q + m)) (Fin (q + m)) ℝ).PosSemidef → 0 ≤ F X)
    (hmono : MonotoneOn (fullRegressionSpectralAverage n C K F) (Spectral.positiveChamber q)) :
    (∫ X, h (principalSymmetricBlock (Fin.castAdd m) X)
      ∂nonsingularWishartMeasure n (regressionScale K C)) *
      (∫ X, F X ∂nonsingularWishartMeasure n (regressionScale K C)) ≤
      ∫ X, h (principalSymmetricBlock (Fin.castAdd m) X) * F X
        ∂nonsingularWishartMeasure n (regressionScale K C) := by
  have hnq : (q : ℝ) - 1 < n := by
    push_cast at hn
    linarith [Nat.cast_nonneg (α := ℝ) m]
  letI := Spectral.laguerreLaw_isProbability hnq
  have hselected := hHM.comp_measurePreserving
    (show MeasurePreserving (principalSymmetricBlock (Fin.castAdd m))
      (nonsingularWishartMeasure n (regressionScale K C)) (nonsingularWishartMeasure n 1) from
      ⟨measurable_principalSymmetricBlock _, map_regressionSelectedBlock hn K hC⟩)
  have hremaining := hFM.wishart n (regressionScale K C)
  have hjoint := (hselected.mul hremaining).integrable
  have hfi : Integrable f (regressionEigenLaw q n) := by
    have hi := (measurePreserving_regressionSpectralMatrix hnq).integrable_comp_of_integrable
      hHM.integrable
    have hi' : Integrable (fun x : (Fin q → ℝ) × Spectral.Orth q => f x.1)
        ((regressionEigenLaw q n).prod (haarProb (Spectral.Orth q))) := by
      apply hi.congr
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae
        (Spectral.ae_laguerreLaw_mem_chamber hnq)] with x hx
      exact hspectral x.1 hx x.2
    simpa only [integral_const, probReal_univ, one_smul] using hi'.integral_prod_left
  rw [integral_fullRegression_selected_spectral hn K hC hh hspectral,
    integral_fullRegression_remaining_spectral hn K hC hFm hremaining.integrable,
    integral_fullRegression_joint_spectral hn K hC hspectral hFm hjoint]
  exact integral_laguerre_mul_ge hnq hfm
    (measurable_fullRegressionSpectralAverage n C K hFm) hf0
    (fullRegressionSpectralAverage_test_nonneg n C K hF0) hfmono hmono hfi
    (integrable_fullRegressionSpectralAverage hn K hC hFm hremaining.integrable)
    (integrable_selected_mul_fullRegressionSpectralAverage hn K hC hspectral hFm hjoint)

end Wishart
end
end CanonicalSource68

section CanonicalSource69
/- Source: Wishart/TraceRegressionComparison.lean -/



/-!
# Actual regression comparisons for finite positive trace supports

Rectangular congruence pulls a positive trace form back to a positive trace
form. Conditioning on other Gaussian rows only adds a nonnegative constant.
Thus the N≥2 scalar comparison gives the exact alpha≥q+1 selected threshold,
independently of all remaining compression ranks.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open WishartVerification
open scoped Matrix MatrixOrder Matrix.Norms.Operator InnerProductSpace RealInnerProductSpace

namespace WishartVerification

theorem inner_symmetricCongruence {p r : ℕ}
    (D : SymmetricMatrix p) (L : Matrix (Fin p) (Fin r) ℝ)
    (X : SymmetricMatrix r) :
    ⟪D, Matrix.symmetricCongruenceLinearMap L X⟫_ℝ =
      ⟪Matrix.symmetricCongruenceLinearMap Lᵀ D, X⟫_ℝ := by
  simp only [selfAdjoint.inner_eq_trace_mul,
    Matrix.coe_symmetricCongruenceLinearMap_apply, Matrix.transpose_transpose]
  calc
    (L * (X : Matrix (Fin r) (Fin r) ℝ) * Lᵀ * (D : Matrix (Fin p) (Fin p) ℝ)).trace =
        (L * ((X : Matrix (Fin r) (Fin r) ℝ) * (Lᵀ * (D : Matrix (Fin p) (Fin p) ℝ)))).trace := by
      simp only [Matrix.mul_assoc]
    _ = (((X : Matrix (Fin r) (Fin r) ℝ) * (Lᵀ * (D : Matrix (Fin p) (Fin p) ℝ))) * L).trace :=
      Matrix.trace_mul_comm _ _
    _ = ((X : Matrix (Fin r) (Fin r) ℝ) * (Lᵀ * (D : Matrix (Fin p) (Fin p) ℝ) * L)).trace := by
      rw [Matrix.mul_assoc]

variable {p : ℕ} {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]

theorem traceMaximumProduct_add_congruence {r : ℕ}
    (ε : ℝ) (c a b : κ → ι → ℝ) (D : κ → ι → SymmetricMatrix p)
    (B : SymmetricMatrix p) (L : Matrix (Fin p) (Fin r) ℝ) (X : SymmetricMatrix r) :
    traceMaximumProduct ε c a b D (B + Matrix.symmetricCongruenceLinearMap L X) =
      traceMaximumProduct ε (fun i j => c i j + ⟪D i j, B⟫_ℝ) a b
        (fun i j => Matrix.symmetricCongruenceLinearMap Lᵀ (D i j)) X := by
  unfold traceMaximumProduct
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  funext j
  have hadd := (traceFunctional (D i j)).map_add B
    (Matrix.symmetricCongruenceLinearMap L X)
  simp only [traceFunctional_apply] at hadd
  rw [hadd, inner_symmetricCongruence]
  congr 2
  ring

theorem continuous_traceMaximumProduct (ε : ℝ) (c a b : κ → ι → ℝ)
    (D : κ → ι → SymmetricMatrix p) (ha : ∀ i j, 0 ≤ a i j) :
    Continuous (traceMaximumProduct ε c a b D) := by
  apply continuous_finsetProd
  intro i _
  apply continuous_finiteMaximum
  intro j
  exact continuous_const.mul ((Real.continuous_rpow_const (ha i j)).comp
    (continuous_const.add (traceFunctional (D i j)).continuous))

theorem matrixTestAllMoments_traceMaximumProduct
    (ε : ℝ) (c a b : κ → ι → ℝ) (D : κ → ι → SymmetricMatrix p)
    (ha : ∀ i j, 0 ≤ a i j) :
    MatrixTestAllMoments (traceMaximumProduct ε c a b D) := by
  intro Ω _ μ _ X hXm hX hentries
  apply HasAllFiniteMoments.finset_prod Finset.univ
  intro i _
  apply hasAllFiniteMoments_finiteMaximum
  intro j
  have htrace : HasAllFiniteMoments (fun z => ⟪D i j, X z⟫_ℝ) μ := by
    simp only [selfAdjoint.inner_eq_trace_mul, Matrix.trace]
    exact HasAllFiniteMoments.finset_sum (μ := μ) Finset.univ _
      (fun u _ => HasAllFiniteMoments.matrix_right_mul_entry
        (fun z => (X z : Matrix (Fin p) (Fin p) ℝ))
        (D i j : Matrix (Fin p) (Fin p) ℝ) hentries u u)
  exact (((HasAllFiniteMoments.const (ε + c i j)).add htrace).rpow (ha i j)).const_mul
    (Real.exp (b i j))

end WishartVerification

namespace Wishart

variable {p : ℕ} {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]

theorem scalarRadialTestMonotone_traceMaximumProduct
    {r : ℕ} {N : ℝ} (hN : (r : ℝ) < N) (hNtwo : 2 ≤ N)
    (c a b : κ → ι → ℝ) (D : κ → ι → SymmetricMatrix p)
    (hc : ∀ i j, 0 ≤ c i j) (ha : ∀ i j, 0 ≤ a i j)
    (hD : ∀ i j, (D i j : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    ScalarRadialTestMonotone N r (traceMaximumProduct 0 c a b D) := by
  intro B hB L v
  let T := radialLiftMatrix v L
  let c' := fun i j => c i j + ⟪D i j, B⟫_ℝ
  let D' := fun i j => Matrix.symmetricCongruenceLinearMap Tᵀ (D i j)
  have hc' : ∀ i j, 0 ≤ c' i j := fun i j =>
    add_nonneg (hc i j) (inner_nonneg_of_posSemidef (hD i j) hB)
  have hD' : ∀ i j, (D' i j : Matrix (Fin (1 + r)) (Fin (1 + r)) ℝ).PosSemidef := by
    intro i j
    simpa only [D', Matrix.coe_symmetricCongruenceLinearMap_apply,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      (hD i j).mul_mul_conjTranspose_same Tᵀ
  have heq (t : ℝ) (z : ScalarRegressionNoise r) :
      traceMaximumProduct 0 c a b D (B + linearRadialInput L v (Real.sqrt t) z) =
        traceMaximumProduct 0 c' a b D' (scalarRadialMatrix (Real.sqrt t) z) := by
    rw [← radialLiftMatrix_scalarRadialMatrix, traceMaximumProduct_add_congruence]
  simpa only [heq] using monotoneOn_scalarRadial_traceMaximumProduct hN hNtwo c' a b D' hc' ha hD'

/-- The actual conditional comparison underlying Theorem 5.2 for finite positive
trace supports. Its only additional degree condition is alpha≥q+1. -/
theorem monotoneOn_fullRegressionSpectralAverage_traceMaximumProduct
    {q m : ℕ} {n : ℝ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (hdegree : (q : ℝ) + 1 ≤ n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (K : Matrix (Fin q) (Fin m) ℝ)
    (c a b : κ → ι → ℝ) (D : κ → ι → SymmetricMatrix (q + m))
    (hc : ∀ i j, 0 ≤ c i j) (ha : ∀ i j, 0 ≤ a i j)
    (hD : ∀ i j, (D i j : Matrix (Fin (q + m)) (Fin (q + m)) ℝ).PosSemidef) :
    MonotoneOn (fullRegressionSpectralAverage n C K (traceMaximumProduct 0 c a b D))
      (Spectral.positiveChamber q) := by
  have hN : (m : ℝ) < n - q + 1 := by
    push_cast at hn
    linarith
  exact monotoneOn_fullRegressionSpectralAverage_test hn hC K
    (continuous_traceMaximumProduct 0 c a b D ha).measurable
    (matrixTestAllMoments_traceMaximumProduct 0 c a b D ha)
    (scalarRadialTestMonotone_traceMaximumProduct hN (by linarith) c a b D hc ha hD)

end Wishart
end
end CanonicalSource69

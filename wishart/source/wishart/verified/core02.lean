module

public import wishart.verified.core01
public import Mathlib.Analysis.Normed.Operator.Prod
public import tau_ceti.probability.stochastic_order
public import tau_ceti.probability.distributions.noncentral_chi_squared.stochastic_order
public import tau_ceti.probability.distributions.noncentral_chi_squared.gaussian
public import tau_ceti.probability.distributions.noncentral_chi_squared.moments
public import tau_ceti.representation_theory.compact.haar
public import tau_ceti.topology.algebra.unitary_group
public import tau_ceti.analysis.matrix.eigenvalues
public import tau_ceti.linear_algebra.matrix.alternating

/- Generated ordinary proof stage. See audit/staged_core/Core02/manifest.json. -/

@[expose] public section

section CanonicalSource25
/- Source: Wishart/ParametricTemperate.lean -/



/-!
# Differentiation of polynomial-growth expectations

Uniform domination on a compact parameter interval is derived from the
polynomial bounds in `HasTemperateGrowth`.  Every finite moment of the random
input is used to justify differentiation; no formal interchange is assumed.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace WishartVerification

theorem hasTemperateGrowth_prodMk {D E F : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : D → E} {g : D → F} (hf : f.HasTemperateGrowth) (hg : g.HasTemperateGrowth) :
    (fun x => (f x, g x)).HasTemperateGrowth := by
  have h := ((ContinuousLinearMap.inl ℝ E F).hasTemperateGrowth.comp hf).add
    ((ContinuousLinearMap.inr ℝ E F).hasTemperateGrowth.comp hg)
  have heq :
      ((ContinuousLinearMap.inl ℝ E F : E → E × F) ∘ f) +
        ((ContinuousLinearMap.inr ℝ E F : F → E × F) ∘ g) =
      fun x => (f x, g x) := by
    funext x
    simp only [Function.comp_apply, Pi.add_apply, ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add]
  rw [heq] at h
  exact h

theorem allFiniteNormMoments_prod {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    {μ : Measure E} {ν : Measure F} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : HasAllFiniteMoments (fun x : E => ‖x‖) μ)
    (hν : HasAllFiniteMoments (fun y : F => ‖y‖) ν) :
    HasAllFiniteMoments (fun x : E × F => ‖x‖) (μ.prod ν) := by
  have hb := (hμ.comp_measurePreserving (measurePreserving_fst (μ := μ) (ν := ν))).add
    (hν.comp_measurePreserving (measurePreserving_snd (μ := μ) (ν := ν)))
  intro q hq
  apply (hb q hq).mono'
    (show AEStronglyMeasurable (fun x : E × F => ‖x‖) (μ.prod ν) from by
      simpa only [Prod.norm_def] using
        ((measurable_fst.norm).max measurable_snd.norm).aestronglyMeasurable)
  filter_upwards with x
  change ‖‖x‖‖ ≤ ‖x.1‖ + ‖x.2‖
  rw [norm_norm, Prod.norm_def]
  exact max_le (le_add_of_nonneg_right (norm_nonneg _))
    (le_add_of_nonneg_left (norm_nonneg _))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def parameterDerivative (F : ℝ × E → ℝ) (p : ℝ × E) : ℝ :=
  fderiv ℝ F p (1, 0)

theorem hasTemperateGrowth_parameterDerivative {F : ℝ × E → ℝ}
    (hF : F.HasTemperateGrowth) : (parameterDerivative F).HasTemperateGrowth := by
  have heq : parameterDerivative F =
      (ContinuousLinearMap.apply ℝ ℝ (1, (0 : E))) ∘ fderiv ℝ F := by
    funext p
    simp only [parameterDerivative, Function.comp_apply, ContinuousLinearMap.apply_apply]
  rw [heq]
  exact (ContinuousLinearMap.apply ℝ ℝ (1, (0 : E))).hasTemperateGrowth.comp
    (hasTemperateGrowth_fderiv hF)

theorem hasDerivAt_parameter_slice {F : ℝ × E → ℝ} (hF : F.HasTemperateGrowth)
    (x : E) (t : ℝ) : HasDerivAt (fun s => F (s, x)) (parameterDerivative F (t, x)) t := by
  have hpair : HasDerivAt (fun s : ℝ => (s, x)) (1, 0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  exact (hF.1.differentiable (by simp) (t, x)).hasFDerivAt.comp_hasDerivAt t hpair

theorem norm_temperate_uniform_parameter {F : ℝ × E → ℝ}
    (hF : F.HasTemperateGrowth) (t : ℝ) :
    ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ s ∈ Set.Icc (t - 1) (t + 1), ∀ x : E,
      ‖F (s, x)‖ ≤ C * (1 + ‖x‖) ^ k := by
  obtain ⟨k, M, hM⟩ := hF.2 0
  refine ⟨k, max M 0 * (|t| + 2) ^ k, by positivity, ?_⟩
  intro s hs x
  have hsleft : t - 1 ≤ s := hs.1
  have hsright : s ≤ t + 1 := hs.2
  have hst : |s - t| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hsabs : |s| ≤ |t| + 1 := by
    calc
      |s| = |(s - t) + t| := by congr 1; ring
      _ ≤ |s - t| + |t| := by
        simpa only [Real.norm_eq_abs] using norm_add_le (s - t) t
      _ ≤ 1 + |t| := by linarith
      _ = _ := add_comm _ _
  have hnorm : 1 + ‖(s, x)‖ ≤ (|t| + 2) * (1 + ‖x‖) := by
    rw [Prod.norm_def, Real.norm_eq_abs]
    have hmax : max |s| ‖x‖ ≤ |t| + 1 + ‖x‖ :=
      max_le (hsabs.trans (le_add_of_nonneg_right (norm_nonneg x)))
        (by linarith [abs_nonneg t])
    nlinarith [mul_nonneg (abs_nonneg t) (norm_nonneg x), norm_nonneg x]
  calc
    ‖F (s, x)‖ ≤ M * (1 + ‖(s, x)‖) ^ k := by simpa using hM (s, x)
    _ ≤ max M 0 * ((|t| + 2) * (1 + ‖x‖)) ^ k := by
      exact mul_le_mul (le_max_left _ _)
        (pow_le_pow_left₀ (by positivity) hnorm k)
        (pow_nonneg (by positivity) k) (le_max_right _ _)
    _ = _ := by rw [mul_pow]; ring

theorem integralDerivativeData_temperate {μ : Measure E} [IsFiniteMeasure μ]
    (hμ : HasAllFiniteMoments (fun x : E => ‖x‖) μ)
    {F : ℝ × E → ℝ} (hF : F.HasTemperateGrowth) (t : ℝ) :
    Nonempty (IntegralDerivativeData μ (fun s x => F (s, x))
      (fun s x => parameterDerivative F (s, x)) t) := by
  have hD := hasTemperateGrowth_parameterDerivative hF
  obtain ⟨k, C, hC, hbound⟩ := norm_temperate_uniform_parameter hD t
  have hslice : (fun x : E => (t, x)).HasTemperateGrowth :=
    hasTemperateGrowth_prodMk (Function.HasTemperateGrowth.const t) Function.HasTemperateGrowth.id
  have hpoly : Integrable (fun x : E => C * (1 + ‖x‖) ^ k) μ := by
    have h := ((HasAllFiniteMoments.const (μ := μ) 1).add hμ).rpow
      (show 0 ≤ (k : ℝ) by positivity)
    simpa only [Real.rpow_natCast] using (h.const_mul C).integrable
  refine ⟨{
    neighborhood := Set.Icc (t - 1) (t + 1)
    neighborhood_mem := Icc_mem_nhds (by linarith) (by linarith)
    bound := fun x => C * (1 + ‖x‖) ^ k
    measurable_near := Filter.Eventually.of_forall fun s =>
      (hF.1.continuous.comp (by fun_prop)).aestronglyMeasurable
    integrable_at := integrable_temperate_of_allNormMoments hμ (hF.comp hslice)
    derivative_measurable := (hD.1.continuous.comp (by fun_prop)).aestronglyMeasurable
    derivative_bound := Filter.Eventually.of_forall fun x s hs => hbound s hs x
    integrable_bound := hpoly
    has_derivative := Filter.Eventually.of_forall fun x s _ => hasDerivAt_parameter_slice hF x s }⟩

theorem hasDerivAt_integral_temperate {μ : Measure E} [IsFiniteMeasure μ]
    (hμ : HasAllFiniteMoments (fun x : E => ‖x‖) μ)
    {F : ℝ × E → ℝ} (hF : F.HasTemperateGrowth) (t : ℝ) :
    HasDerivAt (fun s => ∫ x, F (s, x) ∂μ)
      (∫ x, parameterDerivative F (t, x) ∂μ) t := by
  obtain ⟨h⟩ := integralDerivativeData_temperate hμ hF t
  exact h.hasDerivAt

end WishartVerification
end
end CanonicalSource25

section CanonicalSource26
/- Source: Wishart/RadialExpectationCalculus.lean -/



/-!
# Genuine derivatives of the radial expectation

The random input is a symmetric matrix and a Euclidean vector.  Polynomial
growth and all finite input moments justify the first two derivatives of the
actual integral.  No radial differential equation is assumed here.
-/

noncomputable section

open MeasureTheory Filter Topology Matrix

namespace WishartVerification

variable {p : ℕ}

abbrev RadialInputSpace (p : ℕ) := SymmetricMatrix p × EuclideanSpace ℝ (Fin p)

def radialInput (v : EuclideanSpace ℝ (Fin p)) (r : ℝ) (Y : RadialInputSpace p) :
    SymmetricMatrix p := Y.1 + rankOneSymmetric (Y.2 + r • v)

def radialDirection (v : EuclideanSpace ℝ (Fin p)) (r : ℝ) (Y : RadialInputSpace p) :
    SymmetricMatrix p := symmetricRankDirection v (Y.2 + r • v)

def radialFirstIntegrand (f : SymmetricMatrix p → ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (r : ℝ) (Y : RadialInputSpace p) : ℝ :=
  fderiv ℝ f (radialInput v r Y) (radialDirection v r Y)

def radialSecondIntegrand (f : SymmetricMatrix p → ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (r : ℝ) (Y : RadialInputSpace p) : ℝ :=
  fderiv ℝ (fderiv ℝ f) (radialInput v r Y) (radialDirection v r Y)
      (radialDirection v r Y) + 2 * fderiv ℝ f (radialInput v r Y) (rankOneSymmetric v)

theorem hasTemperateGrowth_radialInput (v : EuclideanSpace ℝ (Fin p)) :
    (fun q : ℝ × RadialInputSpace p => radialInput v q.1 q.2).HasTemperateGrowth := by
  have hW := ((ContinuousLinearMap.fst ℝ (SymmetricMatrix p) (EuclideanSpace ℝ (Fin p))).comp
    (ContinuousLinearMap.snd ℝ ℝ (RadialInputSpace p))).hasTemperateGrowth
  have hz := ((ContinuousLinearMap.snd ℝ (SymmetricMatrix p) (EuclideanSpace ℝ (Fin p))).comp
    (ContinuousLinearMap.snd ℝ ℝ (RadialInputSpace p))).hasTemperateGrowth
  have hr := (ContinuousLinearMap.fst ℝ ℝ (RadialInputSpace p)).hasTemperateGrowth
  exact hW.add (hasTemperateGrowth_rankOneSymmetric.comp
    (hz.add (hr.smul (Function.HasTemperateGrowth.const v))))

theorem hasTemperateGrowth_radialDirection (v : EuclideanSpace ℝ (Fin p)) :
    (fun q : ℝ × RadialInputSpace p => radialDirection v q.1 q.2).HasTemperateGrowth := by
  have hz := ((ContinuousLinearMap.snd ℝ (SymmetricMatrix p) (EuclideanSpace ℝ (Fin p))).comp
    (ContinuousLinearMap.snd ℝ ℝ (RadialInputSpace p))).hasTemperateGrowth
  have hr := (ContinuousLinearMap.fst ℝ ℝ (RadialInputSpace p)).hasTemperateGrowth
  exact (symmetricRankDirection v).hasTemperateGrowth.comp
    (hz.add (hr.smul (Function.HasTemperateGrowth.const v)))

theorem hasDerivAt_radialInput (v : EuclideanSpace ℝ (Fin p))
    (Y : RadialInputSpace p) (r : ℝ) :
    HasDerivAt (fun s => radialInput v s Y) (radialDirection v r Y) r := by
  simpa [radialInput, radialDirection, symmetricRankDirection_comm] using
    (hasDerivAt_rankOne_shift Y.2 v r).const_add Y.1

theorem hasDerivAt_radialDirection (v : EuclideanSpace ℝ (Fin p))
    (Y : RadialInputSpace p) (r : ℝ) :
    HasDerivAt (fun s => radialDirection v s Y) (2 • rankOneSymmetric v) r := by
  simpa only [radialDirection, Function.comp_def, id_eq, one_smul,
    symmetricRankDirection_self] using
    (symmetricRankDirection v).hasFDerivAt.comp_hasDerivAt r
      (((hasDerivAt_id r).smul_const v).const_add Y.2)

theorem hasTemperateGrowth_radialFirstIntegrand {f : SymmetricMatrix p → ℝ}
    (hf : f.HasTemperateGrowth) (v : EuclideanSpace ℝ (Fin p)) :
    (fun q : ℝ × RadialInputSpace p => radialFirstIntegrand f v q.1 q.2).HasTemperateGrowth :=
  (ContinuousLinearMap.apply ℝ ℝ).bilinear_hasTemperateGrowth
    (hasTemperateGrowth_radialDirection v)
    ((hasTemperateGrowth_fderiv hf).comp (hasTemperateGrowth_radialInput v))

theorem hasDerivAt_radialIntegrand {f : SymmetricMatrix p → ℝ}
    (hf : f.HasTemperateGrowth) (v : EuclideanSpace ℝ (Fin p))
    (Y : RadialInputSpace p) (r : ℝ) :
    HasDerivAt (fun s => f (radialInput v s Y)) (radialFirstIntegrand f v r Y) r :=
  (hf.1.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt r
    (hasDerivAt_radialInput v Y r)

theorem hasDerivAt_radialFirstIntegrand {f : SymmetricMatrix p → ℝ}
    (hf : f.HasTemperateGrowth) (v : EuclideanSpace ℝ (Fin p))
    (Y : RadialInputSpace p) (r : ℝ) :
    HasDerivAt (fun s => radialFirstIntegrand f v s Y)
      (radialSecondIntegrand f v r Y) r := by
  have hd := ((hasTemperateGrowth_fderiv hf).1.differentiable
    (by simp) _).hasFDerivAt.comp_hasDerivAt r (hasDerivAt_radialInput v Y r)
  have h := hd.clm_apply (hasDerivAt_radialDirection v Y r)
  simpa [radialFirstIntegrand, radialSecondIntegrand, smul_eq_mul] using h

theorem hasDerivAt_radialExpectation {μ : Measure (RadialInputSpace p)} [IsFiniteMeasure μ]
    (hμ : HasAllFiniteMoments (fun Y : RadialInputSpace p => ‖Y‖) μ)
    {f : SymmetricMatrix p → ℝ} (hf : f.HasTemperateGrowth)
    (v : EuclideanSpace ℝ (Fin p)) (r : ℝ) :
    HasDerivAt (fun s => ∫ Y, f (radialInput v s Y) ∂μ)
      (∫ Y, radialFirstIntegrand f v r Y ∂μ) r := by
  have hF := hf.comp (hasTemperateGrowth_radialInput v)
  have hd := hasDerivAt_integral_temperate hμ hF r
  have heq : (∫ Y, parameterDerivative
      (f ∘ fun q : ℝ × RadialInputSpace p => radialInput v q.1 q.2) (r, Y) ∂μ) =
      ∫ Y, radialFirstIntegrand f v r Y ∂μ := by
    apply integral_congr_ae
    filter_upwards with Y
    exact (hasDerivAt_parameter_slice hF Y r).unique (hasDerivAt_radialIntegrand hf v Y r)
  rw [heq] at hd
  simpa only [Function.comp_apply] using hd

theorem hasDerivAt_radialFirstExpectation {μ : Measure (RadialInputSpace p)} [IsFiniteMeasure μ]
    (hμ : HasAllFiniteMoments (fun Y : RadialInputSpace p => ‖Y‖) μ)
    {f : SymmetricMatrix p → ℝ} (hf : f.HasTemperateGrowth)
    (v : EuclideanSpace ℝ (Fin p)) (r : ℝ) :
    HasDerivAt (fun s => ∫ Y, radialFirstIntegrand f v s Y ∂μ)
      (∫ Y, radialSecondIntegrand f v r Y ∂μ) r := by
  have hF := hasTemperateGrowth_radialFirstIntegrand hf v
  have hd := hasDerivAt_integral_temperate hμ hF r
  have heq : (∫ Y, parameterDerivative
      (fun q : ℝ × RadialInputSpace p => radialFirstIntegrand f v q.1 q.2) (r, Y) ∂μ) =
      ∫ Y, radialSecondIntegrand f v r Y ∂μ := by
    apply integral_congr_ae
    filter_upwards with Y
    exact (hasDerivAt_parameter_slice hF Y r).unique
      (hasDerivAt_radialFirstIntegrand hf v Y r)
  rw [heq] at hd
  exact hd

end WishartVerification
end
end CanonicalSource26

section CanonicalSource27
/- Source: Wishart/RadialGenerator.lean -/



/-!
# The radial generator on the actual symmetric matrix space

The second derivative is the actual derivative of the Fréchet derivative.
Coordinate contractions are expanded using the Euclidean coordinate basis.
-/

noncomputable section

open Matrix
open scoped BigOperators

namespace WishartVerification

variable {p : ℕ}

def coordinateVector (i : Fin p) : EuclideanSpace ℝ (Fin p) :=
  WithLp.toLp 2 (Pi.single i 1)

@[simp] theorem coordinateVector_apply (i j : Fin p) :
    coordinateVector i j = if j = i then 1 else 0 := by
  simp [coordinateVector, Pi.single_apply, eq_comm]

theorem sum_coordinateVector (x : EuclideanSpace ℝ (Fin p)) :
    (∑ i, x i • coordinateVector i) = x := by
  apply PiLp.ext
  intro j
  simp [coordinateVector_apply]

theorem map_sum_coordinateVector {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : EuclideanSpace ℝ (Fin p) →L[ℝ] F) (x : EuclideanSpace ℝ (Fin p)) :
    (∑ i, x i • L (coordinateVector i)) = L x := by
  simp only [← map_smul]
  rw [← map_sum, sum_coordinateVector]

def symmetricSecondDerivative (f : SymmetricMatrix p → ℝ) (X H K : SymmetricMatrix p) : ℝ :=
  fderiv ℝ (fderiv ℝ f) X K H

theorem symmetricSecondDerivative_eq {f : SymmetricMatrix p → ℝ}
    (hf : f.HasTemperateGrowth) (X H K : SymmetricMatrix p) :
    symmetricSecondDerivative f X H K =
      fderiv ℝ (fun Y => fderiv ℝ f Y H) X K := by
  have h := ((hasTemperateGrowth_fderiv hf).1.differentiable (by simp) X).hasFDerivAt
  rw [(h.clm_apply (hasFDerivAt_const H X)).fderiv]
  simp [symmetricSecondDerivative]

def radialCovarianceContraction (f : SymmetricMatrix p → ℝ) (X : SymmetricMatrix p)
    (v : EuclideanSpace ℝ (Fin p)) (B : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  ∑ i, ∑ j, B i j * symmetricSecondDerivative f X
    (symmetricRankDirection v (coordinateVector i))
    (symmetricRankDirection v (coordinateVector j))

def symmetricRadialGenerator (N : ℝ) (v : EuclideanSpace ℝ (Fin p))
    (f : SymmetricMatrix p → ℝ) (X : SymmetricMatrix p) : ℝ :=
  2 * N * fderiv ℝ f X (rankOneSymmetric v) +
    radialCovarianceContraction f X v (X : Matrix (Fin p) (Fin p) ℝ)

theorem radialCovarianceContraction_add (f : SymmetricMatrix p → ℝ) (X : SymmetricMatrix p)
    (v : EuclideanSpace ℝ (Fin p)) (A B : Matrix (Fin p) (Fin p) ℝ) :
    radialCovarianceContraction f X v (A + B) =
      radialCovarianceContraction f X v A + radialCovarianceContraction f X v B := by
  simp [radialCovarianceContraction, add_mul, Finset.sum_add_distrib]

theorem radialCovarianceContraction_rankOne (f : SymmetricMatrix p → ℝ)
    (X : SymmetricMatrix p) (v w : EuclideanSpace ℝ (Fin p)) :
    radialCovarianceContraction f X v (rankOneSymmetric w : Matrix (Fin p) (Fin p) ℝ) =
      symmetricSecondDerivative f X (symmetricRankDirection v w) (symmetricRankDirection v w) := by
  rw [← map_sum_coordinateVector (symmetricRankDirection v) w]
  simp only [radialCovarianceContraction, coe_rankOneSymmetric, Matrix.vecMulVec_apply,
    symmetricSecondDerivative, map_sum, map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem radialCovarianceContraction_eq_directional_sum
    (f : SymmetricMatrix p → ℝ) (X W : SymmetricMatrix p)
    (v : EuclideanSpace ℝ (Fin p)) :
    radialCovarianceContraction f X v (W : Matrix (Fin p) (Fin p) ℝ) =
      ∑ i, symmetricSecondDerivative f X
        (symmetricRankDirection v (coordinateVector i))
        (symmetricRankDirection v (symmetricMatrixAction W (coordinateVector i))) := by
  have hW := (selfAdjoint.isHermitian_coe W).isSymm
  unfold radialCovarianceContraction
  apply Finset.sum_congr rfl
  intro i hi
  rw [← map_sum_coordinateVector (symmetricRankDirection v)
    (symmetricMatrixAction W (coordinateVector i))]
  simp only [symmetricSecondDerivative, map_sum, map_smul,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  simp [symmetricMatrixAction_apply, coordinateVector, Matrix.toLpLin_apply,
    Matrix.mulVec_single_one, Matrix.col_apply, hW.apply]

theorem radialFirstIntegrand_eq_coordinate_sum (f : SymmetricMatrix p → ℝ)
    (v : EuclideanSpace ℝ (Fin p)) (r : ℝ) (Y : RadialInputSpace p) :
    radialFirstIntegrand f v r Y = ∑ i, (Y.2 + r • v) i *
      fderiv ℝ f (radialInput v r Y) (symmetricRankDirection v (coordinateVector i)) := by
  rw [radialFirstIntegrand, radialDirection,
    ← map_sum_coordinateVector (symmetricRankDirection v) (Y.2 + r • v)]
  simp [map_sum, map_smul, smul_eq_mul]

theorem symmetricRadialGenerator_decomposition (N : ℝ)
    (f : SymmetricMatrix p → ℝ) (v : EuclideanSpace ℝ (Fin p))
    (r : ℝ) (Y : RadialInputSpace p) :
    symmetricRadialGenerator N v f (radialInput v r Y) =
      radialSecondIntegrand f v r Y +
        radialCovarianceContraction f (radialInput v r Y) v (Y.1 : Matrix (Fin p) (Fin p) ℝ) +
        2 * (N - 1) * fderiv ℝ f (radialInput v r Y) (rankOneSymmetric v) := by
  rw [symmetricRadialGenerator]
  have he : (radialInput v r Y : Matrix (Fin p) (Fin p) ℝ) =
      (Y.1 : Matrix (Fin p) (Fin p) ℝ) +
        (rankOneSymmetric (Y.2 + r • v) : Matrix (Fin p) (Fin p) ℝ) := rfl
  rw [he, radialCovarianceContraction_add, radialCovarianceContraction_rankOne]
  dsimp [radialSecondIntegrand, radialDirection, symmetricSecondDerivative]
  ring

end WishartVerification
end
end CanonicalSource27

section CanonicalSource28
/- Source: Wishart/DiffusionChainRule.lean -/



/-!
# Chain rule for the radial diffusion

The derivatives in this file are actual Fréchet derivatives. The exponential
chain rule explains the nonnegative square in equation (9) of the manuscript.
-/

noncomputable section

open Matrix MeasureTheory Filter
open scoped Matrix Topology BigOperators

namespace WishartVerification

section DifferentialIdentities

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {g : E → ℝ} {x : E}

theorem fderiv_exp_comp_apply (hg : DifferentiableAt ℝ g x) (H : E) :
    fderiv ℝ (fun y => Real.exp (g y)) x H =
      Real.exp (g x) * fderiv ℝ g x H := by
  rw [hg.hasFDerivAt.exp.fderiv]
  simp

theorem second_fderiv_exp_comp_apply
    (hg : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ g y) (H K : E)
    (hgH : DifferentiableAt ℝ (fun y => fderiv ℝ g y H) x) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => Real.exp (g z)) y H) x K =
      Real.exp (g x) *
        (fderiv ℝ (fun y => fderiv ℝ g y H) x K +
          fderiv ℝ g x H * fderiv ℝ g x K) := by
  have hgx : DifferentiableAt ℝ g x := mem_of_mem_nhds hg
  have heq : (fun y => fderiv ℝ (fun z => Real.exp (g z)) y H) =ᶠ[𝓝 x]
      (fun y => Real.exp (g y) * fderiv ℝ g y H) := by
    filter_upwards [hg] with y hy
    exact fderiv_exp_comp_apply hy H
  have hd := hgx.hasFDerivAt.exp.mul hgH.hasFDerivAt
  rw [heq.fderiv_eq]
  change fderiv ℝ ((fun y => Real.exp (g y)) *
    (fun y => fderiv ℝ g y H)) x K = _
  rw [hd.fderiv]
  simp
  ring

end DifferentialIdentities

variable {n : Type*} [Fintype n] [DecidableEq n]

def carreDuChamp (v : n → ℝ) (V : Matrix n n ℝ)
    (D E : Matrix n n ℝ → ℝ) : ℝ :=
  ∑ i, ∑ j, V i j * D (symRankOne v (Pi.single i 1)) *
    E (symRankOne v (Pi.single j 1))

theorem driftDiffusion_exp_forms (N e : ℝ) (v : n → ℝ) (V : Matrix n n ℝ)
    (D : Matrix n n ℝ → ℝ) (D₂ : Matrix n n ℝ → Matrix n n ℝ → ℝ) :
    driftDiffusion N v V (fun H => e * D H)
      (fun H K => e * (D₂ H K + D H * D K)) =
      e * (driftDiffusion N v V D D₂ + carreDuChamp v V D D) := by
  have hterm (i j : n) :
      V i j * (e * (D₂ (symRankOne v (Pi.single i 1))
          (symRankOne v (Pi.single j 1)) +
        D (symRankOne v (Pi.single i 1)) * D (symRankOne v (Pi.single j 1)))) =
      e * (V i j * D₂ (symRankOne v (Pi.single i 1))
        (symRankOne v (Pi.single j 1))) +
      e * (V i j * D (symRankOne v (Pi.single i 1)) *
        D (symRankOne v (Pi.single j 1))) := by ring
  simp only [driftDiffusion, carreDuChamp, hterm,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem carreDuChamp_of_rankOne_coordinates (v a : n → ℝ)
    (V : Matrix n n ℝ) (D : Matrix n n ℝ → ℝ)
    (hD : ∀ i, D (symRankOne v (Pi.single i 1)) = 2 * a i) :
    carreDuChamp v V D D = 4 * (a ⬝ᵥ (V *ᵥ a)) := by
  simp only [carreDuChamp, hD, dotProduct, Matrix.mulVec,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem carreDuChamp_nonneg_of_rankOne_coordinates (v a : n → ℝ)
    {V : Matrix n n ℝ} (hV : V.PosSemidef) (D : Matrix n n ℝ → ℝ)
    (hD : ∀ i, D (symRankOne v (Pi.single i 1)) = 2 * a i) :
    0 ≤ carreDuChamp v V D D := by
  rw [carreDuChamp_of_rankOne_coordinates v a V D hD]
  apply mul_nonneg (by norm_num)
  simpa only [star_trivial] using hV.dotProduct_mulVec_nonneg a

end WishartVerification
end
end CanonicalSource28

section CanonicalSource29
/- Source: Wishart/CompressionLogCalculus.lean -/



/-!
# Actual derivatives of compressed logarithmic determinants

This module connects the algebraic trace computation to Fréchet derivatives
on the symmetric matrix space.  The lower bound uses positive semidefinite
matrix order, rather than an entrywise order.
-/

noncomputable section

open Matrix Filter Topology
open scoped Matrix.Norms.Operator BigOperators

namespace WishartVerification

variable {p : ℕ} {k : Type*} [Fintype k] [DecidableEq k]

def compressionLog (ε : ℝ) (B : Matrix k k ℝ) (M : Matrix (Fin p) k ℝ)
    (X : SymmetricMatrix p) : ℝ := Real.log (regularizedCompression ε B M X).det

theorem hasFDerivAt_regularizedCompression (ε : ℝ) (B : Matrix k k ℝ)
    (M : Matrix (Fin p) k ℝ) (X : SymmetricMatrix p) :
    HasFDerivAt (regularizedCompression ε B M) (compressionCLM M) X :=
  (((compressionCLM M).hasFDerivAt.const_add B).add_const (ε • 1))

theorem hasFDerivAt_compressionLog (ε : ℝ) (B : Matrix k k ℝ)
    (M : Matrix (Fin p) k ℝ) {X : SymmetricMatrix p}
    (hX : IsUnit (regularizedCompression ε B M X).det) :
    HasFDerivAt (compressionLog ε B M)
      ((traceLeftCLM (regularizedCompression ε B M X)⁻¹).comp (compressionCLM M)) X :=
  (hasFDerivAt_logdet hX).comp X (hasFDerivAt_regularizedCompression ε B M X)

theorem trace_compressed_form (Q : Matrix k k ℝ) (M : Matrix (Fin p) k ℝ)
    (H : Matrix (Fin p) (Fin p) ℝ) :
    Matrix.trace (Q * (Mᵀ * H * M)) = Matrix.trace ((M * Q * Mᵀ) * H) := by
  calc
    Matrix.trace (Q * (Mᵀ * H * M)) = Matrix.trace ((Q * Mᵀ * H) * M) := by
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace (M * (Q * Mᵀ * H)) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

theorem trace_compressed_second_form (Q : Matrix k k ℝ) (M : Matrix (Fin p) k ℝ)
    (H K : Matrix (Fin p) (Fin p) ℝ) :
    Matrix.trace (Q * (Mᵀ * K * M) * Q * (Mᵀ * H * M)) =
      Matrix.trace ((M * Q * Mᵀ) * H * (M * Q * Mᵀ) * K) := by
  calc
    Matrix.trace (Q * (Mᵀ * K * M) * Q * (Mᵀ * H * M)) =
        Matrix.trace ((Q * Mᵀ * K * M * Q * Mᵀ * H) * M) := by
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace (M * (Q * Mᵀ * K * M * Q * Mᵀ * H)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (((M * Q * Mᵀ) * K) * ((M * Q * Mᵀ) * H)) := by
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace (((M * Q * Mᵀ) * H) * ((M * Q * Mᵀ) * K)) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

theorem fderiv_compressionLog_apply (ε : ℝ) (B : Matrix k k ℝ)
    (M : Matrix (Fin p) k ℝ) {X : SymmetricMatrix p}
    (hX : IsUnit (regularizedCompression ε B M X).det) (H : SymmetricMatrix p) :
    fderiv ℝ (compressionLog ε B M) X H =
      Matrix.trace ((M * (regularizedCompression ε B M X)⁻¹ * Mᵀ) *
        (H : Matrix (Fin p) (Fin p) ℝ)) := by
  rw [(hasFDerivAt_compressionLog ε B M hX).fderiv]
  exact trace_compressed_form _ _ _

theorem hasFDerivAt_compressionLog_direction (ε : ℝ) (B : Matrix k k ℝ)
    (M : Matrix (Fin p) k ℝ) {X : SymmetricMatrix p}
    (hX : IsUnit (regularizedCompression ε B M X).det) (H : SymmetricMatrix p) :
    HasFDerivAt (fun Y => fderiv ℝ (compressionLog ε B M) Y H)
      ((logdetSecondCLM (regularizedCompression ε B M X) (compressionCLM M H)).comp
        (compressionCLM M)) X := by
  have hraw := (hasFDerivAt_trace_inverse_mul hX (compressionCLM M H)).comp X
    (hasFDerivAt_regularizedCompression ε B M X)
  apply hraw.congr_of_eventuallyEq
  have hc : Continuous (fun Y => (regularizedCompression ε B M Y).det) :=
    (hasTemperateGrowth_regularizedCompression_det ε B M).1.continuous
  filter_upwards [hc.continuousAt.eventually_ne hX.ne_zero] with Y hY
  rw [(hasFDerivAt_compressionLog ε B M (isUnit_iff_ne_zero.mpr hY)).fderiv]
  rfl

theorem second_fderiv_compressionLog_apply (ε : ℝ) (B : Matrix k k ℝ)
    (M : Matrix (Fin p) k ℝ) {X : SymmetricMatrix p}
    (hX : IsUnit (regularizedCompression ε B M X).det) (H K : SymmetricMatrix p) :
    fderiv ℝ (fun Y => fderiv ℝ (compressionLog ε B M) Y H) X K =
      -Matrix.trace ((M * (regularizedCompression ε B M X)⁻¹ * Mᵀ) *
        (H : Matrix (Fin p) (Fin p) ℝ) *
        (M * (regularizedCompression ε B M X)⁻¹ * Mᵀ) *
        (K : Matrix (Fin p) (Fin p) ℝ)) := by
  rw [(hasFDerivAt_compressionLog_direction ε B M hX H).fderiv]
  simp only [ContinuousLinearMap.comp_apply, logdetSecondCLM_apply, compressionCLM_apply]
  rw [trace_compressed_second_form]

def symmetricDirectionalGenerator (N : ℝ) (v : EuclideanSpace ℝ (Fin p))
    (f : SymmetricMatrix p → ℝ) (X : SymmetricMatrix p) : ℝ :=
  2 * N * fderiv ℝ f X (rankOneSymmetric v) +
    ∑ i, ∑ j, (X : Matrix (Fin p) (Fin p) ℝ) i j *
      fderiv ℝ (fun Y => fderiv ℝ f Y (symmetricRankDirection v (coordinateVector i))) X
        (symmetricRankDirection v (coordinateVector j))

theorem symmetricRadialGenerator_eq_directional {f : SymmetricMatrix p → ℝ}
    (hf : f.HasTemperateGrowth) (N : ℝ) (v : EuclideanSpace ℝ (Fin p))
    (X : SymmetricMatrix p) :
    symmetricRadialGenerator N v f X = symmetricDirectionalGenerator N v f X := by
  simp only [symmetricRadialGenerator, symmetricDirectionalGenerator,
    radialCovarianceContraction, symmetricSecondDerivative_eq hf]

theorem symmetricDirectionalGenerator_eq_of_forms
    (f : SymmetricMatrix p → ℝ) (N : ℝ) (v : EuclideanSpace ℝ (Fin p))
    (X : SymmetricMatrix p)
    (D : Matrix (Fin p) (Fin p) ℝ → ℝ)
    (D₂ : Matrix (Fin p) (Fin p) ℝ → Matrix (Fin p) (Fin p) ℝ → ℝ)
    (hD : ∀ H, fderiv ℝ f X H = D H)
    (hD₂ : ∀ H K, fderiv ℝ (fun Y => fderiv ℝ f Y H) X K = D₂ H K) :
    symmetricDirectionalGenerator N v f X =
      driftDiffusion N (fun i => v i) (X : Matrix (Fin p) (Fin p) ℝ) D D₂ := by
  simp only [symmetricDirectionalGenerator, driftDiffusion, hD, hD₂,
    coe_rankOneSymmetric, coe_symmetricRankDirection, symRankOne, coordinateVector]

theorem symmetricDirectionalGenerator_compressionLog (ε : ℝ) (B : Matrix k k ℝ)
    (M : Matrix (Fin p) k ℝ) {X : SymmetricMatrix p}
    (hX : (regularizedCompression ε B M X).PosDef)
    (N : ℝ) (v : EuclideanSpace ℝ (Fin p)) :
    let A := M * (regularizedCompression ε B M X)⁻¹ * Mᵀ
    symmetricDirectionalGenerator N v (compressionLog ε B M) X =
      2 * (N - Matrix.trace (A * (X : Matrix (Fin p) (Fin p) ℝ))) *
        ((fun i => v i) ⬝ᵥ (A *ᵥ fun i => v i)) -
      2 * ((A *ᵥ fun i => v i) ⬝ᵥ
        ((X : Matrix (Fin p) (Fin p) ℝ) *ᵥ (A *ᵥ fun i => v i))) := by
  dsimp only
  have hunit := (Matrix.isUnit_iff_isUnit_det _).mp hX.isUnit
  rw [symmetricDirectionalGenerator_eq_of_forms _ N v X
    (fun H => Matrix.trace ((M * (regularizedCompression ε B M X)⁻¹ * Mᵀ) * H))
    (fun H K => -Matrix.trace ((M * (regularizedCompression ε B M X)⁻¹ * Mᵀ) * H *
      (M * (regularizedCompression ε B M X)⁻¹ * Mᵀ) * K))
    (fderiv_compressionLog_apply ε B M hunit)
    (second_fderiv_compressionLog_apply ε B M hunit)]
  exact driftDiffusion_logdet_forms
    (compressed_inverse_posSemidef hX M).isHermitian.isSymm N _ _

theorem symmetricDirectionalGenerator_compressionLog_nonneg
    {ε : ℝ} (hε : 0 < ε) {B : Matrix k k ℝ} (hB : B.PosSemidef)
    (M : Matrix (Fin p) k ℝ) {X : SymmetricMatrix p}
    (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    {N : ℝ} (hN : (Fintype.card k : ℝ) + 1 ≤ N)
    (v : EuclideanSpace ℝ (Fin p)) :
    0 ≤ symmetricDirectionalGenerator N v (compressionLog ε B M) X := by
  have hQ := regularizedCompression_posDef hε hB M hX
  let A := M * (regularizedCompression ε B M X)⁻¹ * Mᵀ
  have hA : A.PosSemidef := compressed_inverse_posSemidef hQ M
  have hQT : (regularizedCompression ε B M X -
      Mᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * M).PosSemidef := by
    have he : regularizedCompression ε B M X -
        Mᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * M = B + ε • 1 := by
      dsimp [regularizedCompression, compressionCLM_apply]
      abel
    rw [he]
    exact hB.add (Matrix.PosSemidef.one.smul hε.le)
  have hcontract := compressed_inverse_contraction hQ M _ hQT
  have htrace := compressed_trace_le_card hQ M _ hQT
  have hbound := logarithmic_generator_lower_bound hA hcontract htrace N (fun i => v i)
  rw [symmetricDirectionalGenerator_compressionLog ε B M hQ N v]
  apply le_trans _ hbound
  apply mul_nonneg
  · have : 0 ≤ N - (Fintype.card k : ℝ) - 1 := by linarith
    positivity
  · simpa only [star_trivial] using hA.dotProduct_mulVec_nonneg (fun i => v i)

end WishartVerification
end
end CanonicalSource29

section CanonicalSource30
/- Source: Wishart/CompressionProductGenerator.lean -/



/-!
# Positivity of the determinant-product generator

Every differential expression is tied to an actual derivative.  The only rank
restriction is the explicit inequality `size + 1 ≤ N`; the main theorem
discharges it from the dimensions of disjoint partition blocks.
-/

noncomputable section

open Matrix Filter Topology
open scoped BigOperators Matrix.Norms.Operator

namespace WishartVerification

variable {p : ℕ}

structure CompressionData (p : ℕ) where
  size : ℕ
  offset : Matrix (Fin size) (Fin size) ℝ
  linear : Matrix (Fin p) (Fin size) ℝ
  exponent : ℝ

def compressionProduct {ι : Type*} [Fintype ι]
    (D : ι → CompressionData p) (X : SymmetricMatrix p) : ℝ :=
  ∏ i, ((D i).offset + (D i).linearᵀ *
    (X : Matrix (Fin p) (Fin p) ℝ) * (D i).linear).det ^ (D i).exponent

def regularizedCompressionProduct {ι : Type*} [Fintype ι]
    (ε : ℝ) (D : ι → CompressionData p) (X : SymmetricMatrix p) : ℝ :=
  ∏ i, smoothRegularizedDetPower ε (D i).exponent (D i).offset (D i).linear X

def compressionLogSum {ι : Type*} [Fintype ι]
    (ε : ℝ) (D : ι → CompressionData p) (X : SymmetricMatrix p) : ℝ :=
  ∑ i, (D i).exponent * compressionLog ε (D i).offset (D i).linear X

theorem hasTemperateGrowth_regularizedCompressionProduct {ι : Type*} [Fintype ι]
    {ε : ℝ} (hε : 0 < ε) (D : ι → CompressionData p) :
    (regularizedCompressionProduct ε D).HasTemperateGrowth :=
  hasTemperateGrowth_finset_prod Finset.univ _ (fun i _ =>
    hasTemperateGrowth_smoothRegularizedDetPower hε _ _ _)

theorem symmetricDirectionalGenerator_congr {f g : SymmetricMatrix p → ℝ}
    {X : SymmetricMatrix p} (heq : f =ᶠ[𝓝 X] g)
    (N : ℝ) (v : EuclideanSpace ℝ (Fin p)) :
    symmetricDirectionalGenerator N v f X = symmetricDirectionalGenerator N v g X := by
  unfold symmetricDirectionalGenerator
  rw [heq.fderiv_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  have hD : (fun Y => fderiv ℝ f Y (symmetricRankDirection v (coordinateVector i))) =ᶠ[𝓝 X]
      (fun Y => fderiv ℝ g Y (symmetricRankDirection v (coordinateVector i))) :=
    (heq.fderiv (𝕜 := ℝ)).mono fun Y hY =>
      congrArg (fun L : SymmetricMatrix p →L[ℝ] ℝ =>
        L (symmetricRankDirection v (coordinateVector i))) hY
  rw [hD.fderiv_eq]

def symmetricCarreDuChamp (f : SymmetricMatrix p → ℝ)
    (X : SymmetricMatrix p) (v : EuclideanSpace ℝ (Fin p)) : ℝ :=
  ∑ i, ∑ j, (X : Matrix (Fin p) (Fin p) ℝ) i j *
    fderiv ℝ f X (symmetricRankDirection v (coordinateVector i)) *
    fderiv ℝ f X (symmetricRankDirection v (coordinateVector j))

theorem symmetricCarreDuChamp_nonneg (f : SymmetricMatrix p → ℝ)
    {X : SymmetricMatrix p} (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    (v : EuclideanSpace ℝ (Fin p)) : 0 ≤ symmetricCarreDuChamp f X v := by
  let a : Fin p → ℝ := fun i => fderiv ℝ f X (symmetricRankDirection v (coordinateVector i))
  have h := hX.dotProduct_mulVec_nonneg a
  simpa only [star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum, a,
    symmetricCarreDuChamp, mul_comm, mul_left_comm, mul_assoc] using h

theorem symmetricDirectionalGenerator_exp {g : SymmetricMatrix p → ℝ}
    {X : SymmetricMatrix p}
    (hg : ∀ᶠ Y in 𝓝 X, DifferentiableAt ℝ g Y)
    (hD : ∀ H, DifferentiableAt ℝ (fun Y => fderiv ℝ g Y H) X)
    (N : ℝ) (v : EuclideanSpace ℝ (Fin p)) :
    symmetricDirectionalGenerator N v (fun Y => Real.exp (g Y)) X =
      Real.exp (g X) *
        (symmetricDirectionalGenerator N v g X + symmetricCarreDuChamp g X v) := by
  have hgX : DifferentiableAt ℝ g X := mem_of_mem_nhds hg
  simp only [symmetricDirectionalGenerator, symmetricCarreDuChamp,
    fderiv_exp_comp_apply hgX,
    second_fderiv_exp_comp_apply hg _ _ (hD _), mul_add,
    Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  ring

theorem fderiv_linear_combination_apply {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (f : ι → SymmetricMatrix p → ℝ) {X : SymmetricMatrix p}
    (hf : ∀ i, DifferentiableAt ℝ (f i) X) (H : SymmetricMatrix p) :
    fderiv ℝ (fun Y => ∑ i, a i * f i Y) X H =
      ∑ i, a i * fderiv ℝ (f i) X H := by
  rw [(HasFDerivAt.fun_sum (fun i _ => (hf i).hasFDerivAt.const_mul (a i))).fderiv]
  simp

theorem second_fderiv_linear_combination_apply {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (f : ι → SymmetricMatrix p → ℝ) {X : SymmetricMatrix p}
    (hf : ∀ᶠ Y in 𝓝 X, ∀ i, DifferentiableAt ℝ (f i) Y)
    (hD : ∀ i H, DifferentiableAt ℝ (fun Y => fderiv ℝ (f i) Y H) X)
    (H K : SymmetricMatrix p) :
    fderiv ℝ (fun Y => fderiv ℝ (fun Z => ∑ i, a i * f i Z) Y H) X K =
      ∑ i, a i * fderiv ℝ (fun Y => fderiv ℝ (f i) Y H) X K := by
  have heq : (fun Y => fderiv ℝ (fun Z => ∑ i, a i * f i Z) Y H) =ᶠ[𝓝 X]
      (fun Y => ∑ i, a i * fderiv ℝ (f i) Y H) :=
    hf.mono fun Y hY => fderiv_linear_combination_apply a f hY H
  rw [heq.fderiv_eq]
  exact fderiv_linear_combination_apply a (fun i Y => fderiv ℝ (f i) Y H)
    (fun i => hD i H) K

theorem symmetricDirectionalGenerator_linear_combination {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (f : ι → SymmetricMatrix p → ℝ) {X : SymmetricMatrix p}
    (hf : ∀ᶠ Y in 𝓝 X, ∀ i, DifferentiableAt ℝ (f i) Y)
    (hD : ∀ i H, DifferentiableAt ℝ (fun Y => fderiv ℝ (f i) Y H) X)
    (N : ℝ) (v : EuclideanSpace ℝ (Fin p)) :
    symmetricDirectionalGenerator N v (fun Y => ∑ i, a i * f i Y) X =
      ∑ i, a i * symmetricDirectionalGenerator N v (f i) X := by
  have hfx := mem_of_mem_nhds hf
  simp only [symmetricDirectionalGenerator,
    fderiv_linear_combination_apply a f hfx,
    second_fderiv_linear_combination_apply a f hf hD,
    mul_add, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_mul]
  have hcomm (T : ι → Fin p → Fin p → ℝ) :
      (∑ y, ∑ x, ∑ i, T i y x) = ∑ i, ∑ y, ∑ x, T i y x := by
    calc
      (∑ y, ∑ x, ∑ i, T i y x) = ∑ y, ∑ i, ∑ x, T i y x := by
        apply Finset.sum_congr rfl
        intro y hy
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hcomm]
  simp only [mul_assoc, mul_left_comm, mul_comm]

theorem compressionLogSum_differentiable_near {ι : Type*} [Fintype ι]
    (ε : ℝ) (D : ι → CompressionData p) {X : SymmetricMatrix p}
    (hX : ∀ i, IsUnit (regularizedCompression ε (D i).offset (D i).linear X).det) :
    ∀ᶠ Y in 𝓝 X, ∀ i, DifferentiableAt ℝ
      (compressionLog ε (D i).offset (D i).linear) Y := by
  apply Filter.eventually_all.mpr
  intro i
  have hc := (hasTemperateGrowth_regularizedCompression_det ε (D i).offset (D i).linear).1.continuous
  filter_upwards [hc.continuousAt.eventually_ne (hX i).ne_zero] with Y hY
  exact (hasFDerivAt_compressionLog ε _ _ (isUnit_iff_ne_zero.mpr hY)).differentiableAt

theorem regularizedCompressionProduct_eventually_exp {ι : Type*} [Fintype ι]
    {ε : ℝ} (hε : 0 < ε) (D : ι → CompressionData p)
    (hB : ∀ i, (D i).offset.PosSemidef) {X : SymmetricMatrix p}
    (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef) :
    regularizedCompressionProduct ε D =ᶠ[𝓝 X]
      (fun Y => Real.exp (compressionLogSum ε D Y)) := by
  have hnear : ∀ᶠ Y in 𝓝 X, ∀ i,
      smoothRegularizedDetPower ε (D i).exponent (D i).offset (D i).linear Y =
        (regularizedCompression ε (D i).offset (D i).linear Y).det ^ (D i).exponent ∧
      0 < (regularizedCompression ε (D i).offset (D i).linear Y).det := by
    apply Filter.eventually_all.mpr
    intro i
    have he := smoothRegularizedDetPower_eventuallyEq hε (D i).exponent (hB i) (D i).linear hX
    have hc := (hasTemperateGrowth_regularizedCompression_det ε (D i).offset (D i).linear).1.continuous
    exact he.and (hc.continuousAt.eventually (Ioi_mem_nhds
      (regularizedCompression_posDef hε (hB i) (D i).linear hX).det_pos))
  filter_upwards [hnear] with Y hY
  rw [regularizedCompressionProduct, compressionLogSum, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i hi
  rw [(hY i).1, compressionLog, Real.rpow_def_of_pos (hY i).2]
  congr 1
  ring

/-- The actual radial generator of the smooth extension is nonnegative on the
positive cone.  Every compression has its own size and its own exponent. -/
theorem regularizedCompressionProduct_generator_nonneg {ι : Type*} [Fintype ι]
    {ε : ℝ} (hε : 0 < ε) (D : ι → CompressionData p)
    (hB : ∀ i, (D i).offset.PosSemidef) (hη : ∀ i, 0 ≤ (D i).exponent)
    {N : ℝ} (hN : ∀ i, ((D i).size : ℝ) + 1 ≤ N)
    {X : SymmetricMatrix p} (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    (v : EuclideanSpace ℝ (Fin p)) :
    0 ≤ symmetricRadialGenerator N v (regularizedCompressionProduct ε D) X := by
  let f : ι → SymmetricMatrix p → ℝ := fun i => compressionLog ε (D i).offset (D i).linear
  have hunit (i : ι) : IsUnit (regularizedCompression ε (D i).offset (D i).linear X).det :=
    isUnit_iff_ne_zero.mpr (regularizedCompression_posDef hε (hB i) (D i).linear hX).det_pos.ne'
  have hf := compressionLogSum_differentiable_near ε D hunit
  have hD (i : ι) (H : SymmetricMatrix p) :
      DifferentiableAt ℝ (fun Y => fderiv ℝ (f i) Y H) X :=
    (hasFDerivAt_compressionLog_direction ε (D i).offset (D i).linear (hunit i) H).differentiableAt
  have hg : ∀ᶠ Y in 𝓝 X, DifferentiableAt ℝ (compressionLogSum ε D) Y := by
    filter_upwards [hf] with Y hY
    exact DifferentiableAt.fun_sum (fun i _ => (hY i).const_mul (D i).exponent)
  have hgD (H : SymmetricMatrix p) :
      DifferentiableAt ℝ (fun Y => fderiv ℝ (compressionLogSum ε D) Y H) X := by
    have heq : (fun Y => fderiv ℝ (compressionLogSum ε D) Y H) =ᶠ[𝓝 X]
        (fun Y => ∑ i, (D i).exponent * fderiv ℝ (f i) Y H) :=
      hf.mono fun Y hY => fderiv_linear_combination_apply _ f hY H
    exact heq.differentiableAt_iff.mpr
      (DifferentiableAt.fun_sum (fun i _ => (hD i H).const_mul (D i).exponent))
  rw [symmetricRadialGenerator_eq_directional
    (hasTemperateGrowth_regularizedCompressionProduct hε D),
    symmetricDirectionalGenerator_congr
      (regularizedCompressionProduct_eventually_exp hε D hB hX),
    symmetricDirectionalGenerator_exp hg hgD]
  apply mul_nonneg (Real.exp_pos _).le
  apply add_nonneg _ (symmetricCarreDuChamp_nonneg _ hX v)
  change 0 ≤ symmetricDirectionalGenerator N v (fun Y => ∑ i, (D i).exponent * f i Y) X
  rw [symmetricDirectionalGenerator_linear_combination _ f hf hD]
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hη i)
    (symmetricDirectionalGenerator_compressionLog_nonneg hε (hB i) (D i).linear hX
      (by simpa using hN i) v)

end WishartVerification
end
end CanonicalSource30

section CanonicalSource31
/- Source: Wishart/PrincipalNormalization.lean -/



open scoped Classical Matrix
open MeasureTheory

/-!
# Principal products in the actual selected-block normalization

The selected coordinate set is arbitrary. Its covariance determinant is the
exact positive scale factor, while every other principal block is represented
by a coordinate compression of the entire complementary matrix. The source
measure is transported by the already proved whitening/reindexing map law.

All expectation and Lp identities below concern the original Wishart law and
its actual normalized law. Equality of determinant powers is proved on the
positive-definite support, rather than imposed outside that support.
-/

namespace WishartVerification

noncomputable section

variable {p d : ℕ}

abbrev selectedRank (P : PrincipalPartition p d) (j : Fin d) : ℕ :=
  Wishart.selectedDimension (P.block j)

abbrev remainingRank (P : PrincipalPartition p d) (j : Fin d) : ℕ :=
  Wishart.complementDimension (P.block j)

abbrev normalizedPrincipalMatrix (P : PrincipalPartition p d)
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (j : Fin d) :=
  Wishart.normalizedSelectedMatrix (P.block j) Sigma

def principalCrossScale (P : PrincipalPartition p d)
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (j : Fin d) :
    Matrix (Fin (selectedRank P j)) (Fin (remainingRank P j)) ℝ :=
  Wishart.normalizedCrossScale (selectedRank P j) (remainingRank P j)
    (Sigma.submatrix (Wishart.selectedCoordinatesEquiv (P.block j))
      (Wishart.selectedCoordinatesEquiv (P.block j)))

def principalResidualScale (P : PrincipalPartition p d)
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (j : Fin d) :
    Matrix (Fin (remainingRank P j)) (Fin (remainingRank P j)) ℝ :=
  Wishart.selectedSchurScale (selectedRank P j) (remainingRank P j)
    (Sigma.submatrix (Wishart.selectedCoordinatesEquiv (P.block j))
      (Wishart.selectedCoordinatesEquiv (P.block j)))

def normalizedPrincipalMeasure (α : ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ)
    (P : PrincipalPartition p d) (j : Fin d) :
    Measure (SymmetricMatrix (selectedRank P j + remainingRank P j)) :=
  TauCeti.Probability.nonsingularWishartMeasure α
    (Wishart.regressionScale (principalCrossScale P Sigma j) (principalResidualScale P Sigma j))

theorem selectedRank_add_remainingRank (P : PrincipalPartition p d) (j : Fin d) :
    selectedRank P j + remainingRank P j = p :=
  Wishart.selectedDimension_add_complementDimension (P.block j)

theorem selectedRank_pos (P : PrincipalPartition p d) (j : Fin d) :
    0 < selectedRank P j := by
  obtain ⟨a, ha⟩ := P.nonempty j
  exact Fintype.card_pos_iff.mpr ⟨⟨a, ha⟩⟩

theorem remainingRank_pos_of_other_block (P : PrincipalPartition p d)
    (j i : Fin d) (hij : i ≠ j) : 0 < remainingRank P j := by
  obtain ⟨a, ha⟩ := P.nonempty i
  exact Fintype.card_pos_iff.mpr ⟨⟨a,
    fun haj ↦ Finset.disjoint_left.mp (P.disjoint hij) ha haj⟩⟩

theorem principal_regression_shape (P : PrincipalPartition p d)
    {α : ℝ} (hα : (p : ℝ) - 1 < α) (j : Fin d) :
    (((selectedRank P j + remainingRank P j : ℕ) : ℝ) - 1) < α := by
  rw [selectedRank_add_remainingRank]
  exact hα

theorem principal_spectral_shape (P : PrincipalPartition p d)
    {α : ℝ} (hα : (p : ℝ) - 1 < α) (j : Fin d) :
    (selectedRank P j : ℝ) - 1 < α := by
  have h := principal_regression_shape P hα j
  have hm : (0 : ℝ) ≤ remainingRank P j := Nat.cast_nonneg _
  push_cast at h
  linarith

theorem principalResidualScale_posDef (P : PrincipalPartition p d)
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef) (j : Fin d) :
    (principalResidualScale P Sigma j).PosDef :=
  Wishart.selectedSchurScale_posDef
    (hSigma.submatrix (Wishart.selectedCoordinatesEquiv (P.block j)).injective)

theorem normalizedPrincipalMatrix_measurePreserving
    (P : PrincipalPartition p d) {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α) (j : Fin d) :
    MeasurePreserving (normalizedPrincipalMatrix P Sigma j)
      (TauCeti.Probability.nonsingularWishartMeasure α Sigma)
      (normalizedPrincipalMeasure α Sigma P j) :=
  ⟨Wishart.measurable_normalizedSelectedMatrix (P.block j) Sigma,
    Wishart.map_normalizedSelectedMatrix_nonsingularWishartMeasure (P.block j) hSigma hα⟩

def principalMomentScale (P : PrincipalPartition p d)
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (ν : Fin d → ℝ) (j : Fin d) : ℝ :=
  (Sigma.submatrix (fun a : P.block j ↦ (a : Fin p))
    (fun b : P.block j ↦ (b : Fin p))).det ^ ν j

theorem principalMomentScale_pos (P : PrincipalPartition p d)
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef)
    (ν : Fin d → ℝ) (j : Fin d) : 0 < principalMomentScale P Sigma ν j :=
  Real.rpow_pos_of_pos (hSigma.submatrix Subtype.coe_injective).det_pos _

def matrixDetPower {q : ℕ} (η : ℝ) (Y : SymmetricMatrix q) : ℝ :=
  (Y : Matrix (Fin q) (Fin q) ℝ).det ^ η

theorem matrixDetPower_measurable {q : ℕ} (η : ℝ) :
    Measurable (matrixDetPower (q := q) η) :=
  continuous_subtype_val.matrix_det.measurable.pow_const _

def principalLeadingTest (P : PrincipalPartition p d) (ν : Fin d → ℝ) (j : Fin d)
    (Y : SymmetricMatrix (selectedRank P j + remainingRank P j)) : ℝ :=
  matrixDetPower (ν j) (Wishart.principalSymmetricBlock (Fin.castAdd (remainingRank P j)) Y)

theorem principalLeadingTest_measurable (P : PrincipalPartition p d)
    (ν : Fin d → ℝ) (j : Fin d) : Measurable (principalLeadingTest P ν j) :=
  (matrixDetPower_measurable _).comp (Wishart.measurable_principalSymmetricBlock _)

def remainingBlockCoordinates (P : PrincipalPartition p d) (j i : Fin d) (hij : i ≠ j) :
    Fin (Fintype.card (P.block i)) → Fin (remainingRank P j) :=
  Wishart.complementCoordinates (P.block j)
    (fun a ↦ ((Fintype.equivFin (P.block i)).symm a : Fin p))
    (fun a haj ↦ Finset.disjoint_left.mp (P.disjoint hij)
      ((Fintype.equivFin (P.block i)).symm a).property haj)

theorem remainingBlockCoordinates_injective (P : PrincipalPartition p d)
    (j i : Fin d) (hij : i ≠ j) : Function.Injective (remainingBlockCoordinates P j i hij) := by
  intro a b hab
  apply (Fintype.equivFin (P.block i)).symm.injective
  apply Subtype.ext
  have h := (Fintype.equivFin {x : Fin p // x ∉ P.block j}).injective hab
  exact congrArg (fun x : {x : Fin p // x ∉ P.block j} => x.1) h

def remainingCompressionData (P : PrincipalPartition p d) (ν : Fin d → ℝ)
    (J : Finset (Fin d)) (j : Fin d) (i : J.erase j) : CompressionData (remainingRank P j) where
  size := Fintype.card (P.block i)
  offset := 0
  linear := (1 : Matrix (Fin (remainingRank P j)) (Fin (remainingRank P j)) ℝ).submatrix id
    (remainingBlockCoordinates P j i (Finset.mem_erase.mp i.property).1)
  exponent := ν i

def remainingPrincipalTest (P : PrincipalPartition p d) (ν : Fin d → ℝ)
    (J : Finset (Fin d)) (j : Fin d) : SymmetricMatrix (remainingRank P j) → ℝ :=
  compressionProduct (remainingCompressionData P ν J j)

theorem compressionProduct_measurable {m : ℕ} {ι : Type*} [Fintype ι]
    (D : ι → CompressionData m) : Measurable (compressionProduct D) := by
  unfold compressionProduct
  apply Finset.measurable_prod
  intro i hi
  have hM : Continuous (fun X : SymmetricMatrix m ↦
      (D i).offset + (D i).linearᵀ * (X : Matrix (Fin m) (Fin m) ℝ) * (D i).linear) :=
    continuous_const.add ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const)
  exact hM.matrix_det.measurable.pow_const _

theorem remainingPrincipalTest_measurable (P : PrincipalPartition p d) (ν : Fin d → ℝ)
    (J : Finset (Fin d)) (j : Fin d) : Measurable (remainingPrincipalTest P ν J j) :=
  compressionProduct_measurable _

def principalTrailingTest (P : PrincipalPartition p d) (ν : Fin d → ℝ)
    (J : Finset (Fin d)) (j : Fin d)
    (Y : SymmetricMatrix (selectedRank P j + remainingRank P j)) : ℝ :=
  remainingPrincipalTest P ν J j
    (Wishart.principalSymmetricBlock (Fin.natAdd (selectedRank P j)) Y)

theorem principalTrailingTest_measurable (P : PrincipalPartition p d)
    (ν : Fin d → ℝ) (J : Finset (Fin d)) (j : Fin d) :
    Measurable (principalTrailingTest P ν J j) :=
  (remainingPrincipalTest_measurable P ν J j).comp (Wishart.measurable_principalSymmetricBlock _)

def principalJointTest (P : PrincipalPartition p d) (ν : Fin d → ℝ)
    (J : Finset (Fin d)) (j : Fin d)
    (Y : SymmetricMatrix (selectedRank P j + remainingRank P j)) : ℝ :=
  principalLeadingTest P ν j Y * principalTrailingTest P ν J j Y

theorem principalJointTest_measurable (P : PrincipalPartition p d)
    (ν : Fin d → ℝ) (J : Finset (Fin d)) (j : Fin d) :
    Measurable (principalJointTest P ν J j) :=
  (principalLeadingTest_measurable P ν j).mul (principalTrailingTest_measurable P ν J j)

theorem remainingCompression_det_normalized (P : PrincipalPartition p d)
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (ν : Fin d → ℝ)
    (J : Finset (Fin d)) (j : Fin d) (i : J.erase j) (X : SymmetricMatrix p) :
    ((remainingCompressionData P ν J j i).offset +
      (remainingCompressionData P ν J j i).linearᵀ *
        ((Wishart.principalSymmetricBlock (Fin.natAdd (selectedRank P j))
          (normalizedPrincipalMatrix P Sigma j X) : SymmetricMatrix (remainingRank P j)) :
            Matrix (Fin (remainingRank P j)) (Fin (remainingRank P j)) ℝ) *
        (remainingCompressionData P ν J j i).linear).det = principalMinor (P.block i) X := by
  change (0 +
    ((1 : Matrix (Fin (remainingRank P j)) (Fin (remainingRank P j)) ℝ).submatrix id
      (remainingBlockCoordinates P j i (Finset.mem_erase.mp i.property).1))ᵀ *
        ((Wishart.principalSymmetricBlock (Fin.natAdd (selectedRank P j))
          (normalizedPrincipalMatrix P Sigma j X) : SymmetricMatrix (remainingRank P j)) :
            Matrix (Fin (remainingRank P j)) (Fin (remainingRank P j)) ℝ) *
      (1 : Matrix (Fin (remainingRank P j)) (Fin (remainingRank P j)) ℝ).submatrix id
        (remainingBlockCoordinates P j i (Finset.mem_erase.mp i.property).1)).det = _
  rw [zero_add, Matrix.transpose_submatrix, Matrix.transpose_one,
    Matrix.submatrix_one_mul_mul_submatrix_one]
  have h := Wishart.normalizedSelectedMatrix_complementarySubmatrix
    (P.block j) Sigma X
    (fun a : Fin (Fintype.card (P.block i)) ↦ ((Fintype.equivFin (P.block i)).symm a : Fin p))
    (fun a haj ↦ Finset.disjoint_left.mp (P.disjoint (Finset.mem_erase.mp i.property).1)
      ((Fintype.equivFin (P.block i)).symm a).property haj)
  have hdet := congrArg Matrix.det h
  have henumeration := principalMinor_eq_det_enumeration (P.block i) X
    (Fintype.equivFin (P.block i)).symm
  calc
    _ = ((X : Matrix (Fin p) (Fin p) ℝ).submatrix
        (fun a : Fin (Fintype.card (P.block i)) ↦ ((Fintype.equivFin (P.block i)).symm a : Fin p))
        (fun a : Fin (Fintype.card (P.block i)) ↦ ((Fintype.equivFin (P.block i)).symm a : Fin p))).det := by
      simpa only [Wishart.principalSymmetricBlock, Matrix.submatrix_submatrix,
        Function.comp_def, remainingBlockCoordinates, normalizedPrincipalMatrix] using hdet
    _ = principalMinor (P.block i) X := henumeration.symm

theorem principalTrailingTest_normalized (P : PrincipalPartition p d)
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (ν : Fin d → ℝ)
    (J : Finset (Fin d)) (j : Fin d) (X : SymmetricMatrix p) :
    principalTrailingTest P ν J j (normalizedPrincipalMatrix P Sigma j X) =
      principalMomentIntegrand P ν (J.erase j) X := by
  calc
    _ = ∏ i : J.erase j, principalMinor (P.block i) X ^ ν i := by
      unfold principalTrailingTest remainingPrincipalTest compressionProduct
      apply Finset.prod_congr rfl
      intro i hi
      rw [remainingCompression_det_normalized]
      rfl
    _ = principalMomentIntegrand P ν (J.erase j) X :=
      Finset.prod_coe_sort (J.erase j) (fun i => principalMinor (P.block i) X ^ ν i)

theorem principalFactor_eq_scaled_leading (P : PrincipalPartition p d)
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef)
    (ν : Fin d → ℝ) (j : Fin d) (X : SymmetricMatrix p)
    (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    (principalMinor (P.block j) X) ^ ν j = principalMomentScale P Sigma ν j *
      principalLeadingTest P ν j (normalizedPrincipalMatrix P Sigma j X) := by
  have ha : 0 < (Sigma.submatrix (fun a : P.block j ↦ (a : Fin p))
      (fun b : P.block j ↦ (b : Fin p))).det :=
    (hSigma.submatrix Subtype.coe_injective).det_pos
  have hx := principalMinor_pos (P.block j) X hX
  unfold principalLeadingTest matrixDetPower principalMomentScale
  rw [Wishart.normalizedSelectedMatrix_selectedDeterminant (P.block j) hSigma X,
    Real.mul_rpow (inv_nonneg.mpr ha.le) hx.le, Real.inv_rpow ha.le,
    ← mul_assoc, mul_inv_cancel₀ (Real.rpow_pos_of_pos ha (ν j)).ne', one_mul]

theorem principalJointIntegrand_eq_scaled_normalized (P : PrincipalPartition p d)
    {Sigma : Matrix (Fin p) (Fin p) ℝ} (hSigma : Sigma.PosDef)
    (ν : Fin d → ℝ) (J : Finset (Fin d)) (j : Fin d) (hj : j ∈ J)
    (X : SymmetricMatrix p) (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    principalMomentIntegrand P ν J X = principalMomentScale P Sigma ν j *
      principalJointTest P ν J j (normalizedPrincipalMatrix P Sigma j X) := by
  rw [principalJointTest, principalTrailingTest_normalized]
  have hprod := Finset.mul_prod_erase J
    (fun i ↦ (principalMinor (P.block i) X) ^ ν i) hj
  change _ = _ * (_ * ∏ i ∈ J.erase j, (principalMinor (P.block i) X) ^ ν i)
  rw [← mul_assoc, ← principalFactor_eq_scaled_leading P hSigma ν j X hX]
  exact hprod.symm

theorem allFiniteMoments_principalMomentIntegrand
    (P : PrincipalPartition p d) {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (ν : Fin d → ℝ) (hν : ∀ i, 0 ≤ ν i) (J : Finset (Fin d)) :
    HasAllFiniteMoments (principalMomentIntegrand P ν J)
      (TauCeti.Probability.nonsingularWishartMeasure α Sigma) := by
  letI := TauCeti.Probability.isProbabilityMeasure_nonsingularWishartMeasure hSigma hα
  exact HasAllFiniteMoments.finset_prod J _ fun i hi ↦
    (allFiniteMoments_wishart_principalMinor hSigma hα (P.block i)).rpow (hν i)

/-- The exact three moment correspondences before spectral disintegration. -/
theorem principal_normalization_moments
    (P : PrincipalPartition p d) {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (ν : Fin d → ℝ) (J : Finset (Fin d)) (j : Fin d) (hj : j ∈ J) :
    principalMoment α Sigma P ν J = principalMomentScale P Sigma ν j *
      (∫ Y, principalJointTest P ν J j Y ∂normalizedPrincipalMeasure α Sigma P j) ∧
    principalMoment α Sigma P ν {j} = principalMomentScale P Sigma ν j *
      (∫ Y, principalLeadingTest P ν j Y ∂normalizedPrincipalMeasure α Sigma P j) ∧
    principalMoment α Sigma P ν (J.erase j) =
      (∫ Y, principalTrailingTest P ν J j Y ∂normalizedPrincipalMeasure α Sigma P j) := by
  have hmp := normalizedPrincipalMatrix_measurePreserving P hSigma hα j
  have hpos := TauCeti.Probability.ae_posDef_nonsingularWishartMeasure α Sigma
  refine ⟨?_, ?_, ?_⟩
  · exact integral_eq_scaled_of_pullback hmp _ _ _
      (principalJointTest_measurable P ν J j)
      (hpos.mono fun X hX ↦ principalJointIntegrand_eq_scaled_normalized P hSigma ν J j hj X hX)
  · apply integral_eq_scaled_of_pullback hmp _ _ _ (principalLeadingTest_measurable P ν j)
    filter_upwards [hpos] with X hX
    simpa only [principalMomentIntegrand, Finset.prod_singleton] using
      principalFactor_eq_scaled_leading P hSigma ν j X hX
  · have h := integral_eq_scaled_of_pullback hmp (principalMomentIntegrand P ν (J.erase j))
      (principalTrailingTest P ν J j) 1 (principalTrailingTest_measurable P ν J j)
      (ae_of_all _ fun X ↦ by
        simpa only [one_mul] using (principalTrailingTest_normalized P Sigma ν J j X).symm)
    simpa only [one_mul, principalMoment] using h

/-- All orders of moments are transported for the selected, remaining, and
joint normalized tests. This supplies ordinary integrability and the L²
conditions needed for the strict Haar-averaging argument. -/
theorem principal_normalization_allFiniteMoments
    (P : PrincipalPartition p d) {α : ℝ} {Sigma : Matrix (Fin p) (Fin p) ℝ}
    (hSigma : Sigma.PosDef) (hα : (p : ℝ) - 1 < α)
    (ν : Fin d → ℝ) (hν : ∀ i, 0 ≤ ν i)
    (J : Finset (Fin d)) (j : Fin d) (hj : j ∈ J) :
    HasAllFiniteMoments (principalLeadingTest P ν j) (normalizedPrincipalMeasure α Sigma P j) ∧
    HasAllFiniteMoments (principalTrailingTest P ν J j) (normalizedPrincipalMeasure α Sigma P j) ∧
    HasAllFiniteMoments (principalJointTest P ν J j) (normalizedPrincipalMeasure α Sigma P j) := by
  have hmp := normalizedPrincipalMatrix_measurePreserving P hSigma hα j
  have hpos := TauCeti.Probability.ae_posDef_nonsingularWishartMeasure α Sigma
  have hc := (principalMomentScale_pos P hSigma ν j).ne'
  refine ⟨?_, ?_, ?_⟩
  · apply allFiniteMoments_of_scaled_pullback hmp
      (principalMomentIntegrand P ν {j}) _ _ hc (principalLeadingTest_measurable P ν j)
      (allFiniteMoments_principalMomentIntegrand P hSigma hα ν hν {j})
    filter_upwards [hpos] with X hX
    simpa only [principalMomentIntegrand, Finset.prod_singleton] using
      principalFactor_eq_scaled_leading P hSigma ν j X hX
  · exact allFiniteMoments_of_scaled_pullback hmp
      (principalMomentIntegrand P ν (J.erase j)) _ 1 one_ne_zero
      (principalTrailingTest_measurable P ν J j)
      (allFiniteMoments_principalMomentIntegrand P hSigma hα ν hν (J.erase j))
      (ae_of_all _ fun X ↦ by
        simpa only [one_mul] using (principalTrailingTest_normalized P Sigma ν J j X).symm)
  · exact allFiniteMoments_of_scaled_pullback hmp
      (principalMomentIntegrand P ν J) _ _ hc (principalJointTest_measurable P ν J j)
      (allFiniteMoments_principalMomentIntegrand P hSigma hα ν hν J)
      (hpos.mono fun X hX ↦ principalJointIntegrand_eq_scaled_normalized P hSigma ν J j hj X hX)

end

end WishartVerification
end CanonicalSource31

section CanonicalSource32
/- Source: Wishart/SpectralRegression.lean -/



/-!
# The conditional regression model in spectral coordinates

Orthogonal mixing of independent Gaussian rows preserves their full product
law, including for singular within-row covariance. Consequently the conditional
remaining Wishart block at S=O diag(lambda) Oᵀ has the same law as an independent
residual plus the Gram matrix of rows G+diag(sqrt(lambda))OᵀK. The residual and
all rows remain independent in this representation.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace Wishart

def gaussianRowMatrix {q m : ℕ} (z : Fin q → EuclideanSpace ℝ (Fin m)) :
    Matrix (Fin m) (Fin q) ℝ := Matrix.of fun i j => z j i

@[fun_prop] theorem measurable_gaussianRowMatrix {q m : ℕ} :
    Measurable (@gaussianRowMatrix q m) := by
  apply Matrix.measurable_iff.mpr
  intro i j
  exact (measurable_pi_apply i).comp
    ((WithLp.measurable_ofLp 2 (Fin m → ℝ)).comp (measurable_pi_apply j))

def gaussianRowRotation {q m : ℕ} (O : Matrix (Fin q) (Fin q) ℝ)
    (z : Fin q → EuclideanSpace ℝ (Fin m)) : Fin q → EuclideanSpace ℝ (Fin m) :=
  fun j => WithLp.toLp 2 (fun i => ∑ k : Fin q, O j k * z k i)

@[fun_prop] theorem measurable_gaussianRowRotation {q m : ℕ}
    (O : Matrix (Fin q) (Fin q) ℝ) :
    Measurable (gaussianRowRotation (m := m) O) := by
  unfold gaussianRowRotation
  fun_prop

theorem gaussianRowRotation_matrix {q m : ℕ}
    (O : Matrix (Fin q) (Fin q) ℝ) (z : Fin q → EuclideanSpace ℝ (Fin m)) :
    gaussianRowMatrix (gaussianRowRotation O z) = gaussianRowMatrix z * Oᵀ := by
  ext i j
  simp only [gaussianRowMatrix, gaussianRowRotation, Matrix.of_apply,
    PiLp.toLp_apply, Matrix.mul_apply, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

theorem gaussianRowMatrix_withFactor {q m : ℕ}
    (R : Matrix (Fin m) (Fin m) ℝ) (g : Fin m × Fin q → ℝ) :
    gaussianRowMatrix (gaussianRowsWithFactor R g) =
      R * Matrix.of (fun i j => g (i, j)) := gaussianRowsWithFactor_matrix R g

theorem gaussianRowRotation_withFactor {q m : ℕ}
    (O : Matrix (Fin q) (Fin q) ℝ) (R : Matrix (Fin m) (Fin m) ℝ) :
    gaussianRowRotation O ∘ gaussianRowsWithFactor R =
      gaussianRowsWithFactor R ∘ rectangularRotation O := by
  funext g
  have hm : gaussianRowMatrix (gaussianRowRotation O (gaussianRowsWithFactor R g)) =
      gaussianRowMatrix (gaussianRowsWithFactor R (rectangularRotation O g)) := by
    rw [gaussianRowRotation_matrix, gaussianRowMatrix_withFactor,
      gaussianRowMatrix_withFactor, rectangularRotation_matrix, Matrix.mul_assoc]
  funext j
  apply PiLp.ext
  intro i
  exact congrArg (fun M : Matrix (Fin m) (Fin q) ℝ => M i j) hm

/-- Mixing the row index by an orthogonal matrix preserves the literal product
of the covariance-C Gaussian row laws. -/
theorem measurePreserving_gaussianRowRotation {q m : ℕ}
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosSemidef)
    (O : Matrix (Fin q) (Fin q) ℝ) (hO : O * Oᵀ = 1) :
    MeasurePreserving (gaussianRowRotation (m := m) O)
      (Measure.pi (fun _ : Fin q => multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) C))
      (Measure.pi (fun _ : Fin q => multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) C)) := by
  refine ⟨measurable_gaussianRowRotation O, ?_⟩
  have hroot : CFC.sqrt C * (CFC.sqrt C)ᵀ = C := by
    rw [matrix_sqrt_transpose]
    exact CFC.sqrt_mul_sqrt_self C hC.nonneg
  have hpush := (measurePreserving_gaussianRowsWithFactor (q := q) (CFC.sqrt C)).map_eq
  rw [hroot] at hpush
  have hfactor : Measurable (gaussianRowsWithFactor (q := q) (CFC.sqrt C)) := by
    unfold gaussianRowsWithFactor
    fun_prop
  have hrotate : Measurable (rectangularRotation (m := m) O) := by
    exact measurable_rectangularRotation.comp (measurable_const.prodMk measurable_id)
  rw [← hpush, Measure.map_map (measurable_gaussianRowRotation O) hfactor,
    gaussianRowRotation_withFactor, ← Measure.map_map hfactor hrotate,
    map_rectangularRotation_piGaussian O hO]

def regressionNoiseRotation {q m : ℕ} (O : Matrix (Fin q) (Fin q) ℝ) :
    RegressionNoise q m → RegressionNoise q m := Prod.map (gaussianRowRotation O) id

theorem measurePreserving_regressionNoiseRotation {q m : ℕ} (n : ℝ)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosSemidef)
    (O : Matrix (Fin q) (Fin q) ℝ) (hO : O * Oᵀ = 1) :
    MeasurePreserving (regressionNoiseRotation O)
      (regressionNoiseMeasure n q m C) (regressionNoiseMeasure n q m C) :=
  (measurePreserving_gaussianRowRotation hC O hO).prod (MeasurePreserving.id _)

def regressionGramWithMean {q m : ℕ} (M : Matrix (Fin m) (Fin q) ℝ)
    (x : RegressionNoise q m) : SymmetricMatrix m :=
  let Y := M + gaussianRowMatrix x.1
  ⟨Y * Yᵀ + (x.2 : Matrix (Fin m) (Fin m) ℝ),
    Matrix.isHermitian_iff_isSelfAdjoint.mp
      ((show (Y * Yᵀ).IsHermitian from by
        simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
          Matrix.isHermitian_mul_conjTranspose_self Y).add
        (Matrix.isHermitian_iff_isSelfAdjoint.mpr x.2.property))⟩

@[fun_prop] theorem measurable_regressionGramWithMean_uncurry {q m : ℕ} :
    Measurable (fun y : Matrix (Fin m) (Fin q) ℝ × RegressionNoise q m =>
      regressionGramWithMean y.1 y.2) := by
  apply Measurable.subtype_mk
  apply Matrix.measurable_iff.mpr
  intro i j
  simp only [regressionGramWithMean, Matrix.add_apply,
    Matrix.mul_apply, Matrix.transpose_apply]
  apply Measurable.add
  · apply Finset.measurable_sum
    intro a _
    exact (measurable_fst.eval_matrix.add
      (measurable_gaussianRowMatrix.comp (measurable_fst.comp measurable_snd)).eval_matrix).mul
      (measurable_fst.eval_matrix.add
        (measurable_gaussianRowMatrix.comp (measurable_fst.comp measurable_snd)).eval_matrix)
  · exact (measurable_subtype_coe.comp (measurable_snd.comp measurable_snd)).eval_matrix

@[fun_prop] theorem measurable_regressionGramWithMean {q m : ℕ}
    (M : Matrix (Fin m) (Fin q) ℝ) : Measurable (regressionGramWithMean M) :=
  measurable_regressionGramWithMean_uncurry.comp (measurable_const.prodMk measurable_id)

theorem regressionReconstruction_trailing {q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (x : RegressionData q m) :
    principalSymmetricBlock (Fin.natAdd q) (regressionReconstruction K x) =
      regressionGramWithMean (Kᵀ * CFC.sqrt (x.1 : Matrix (Fin q) (Fin q) ℝ)) x.2 := by
  apply Subtype.ext
  ext i j
  have h := congrArg
    (fun A : Matrix (Fin q ⊕ Fin m) (Fin q ⊕ Fin m) ℝ => A (.inr i) (.inr j))
    (regressionReconstruction_submatrix K x)
  simpa only [principalSymmetricBlock, regressionGramWithMean, gaussianRowMatrix,
    Matrix.submatrix_apply, finSumFinEquiv_apply_right, regressionBlockMatrix,
    Matrix.fromBlocks_apply₂₂] using h

theorem regressionGramWithMean_rotation {q m : ℕ}
    (M : Matrix (Fin m) (Fin q) ℝ) (O : Matrix (Fin q) (Fin q) ℝ)
    (hO : O * Oᵀ = 1) (x : RegressionNoise q m) :
    regressionGramWithMean (M * Oᵀ) (regressionNoiseRotation O x) =
      regressionGramWithMean M x := by
  have hOO : Oᵀ * O = 1 := mul_eq_one_comm.mp hO
  apply Subtype.ext
  change (M * Oᵀ + gaussianRowMatrix (gaussianRowRotation O x.1)) *
      (M * Oᵀ + gaussianRowMatrix (gaussianRowRotation O x.1))ᵀ +
      (x.2 : Matrix (Fin m) (Fin m) ℝ) = _
  rw [gaussianRowRotation_matrix, ← Matrix.add_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose]
  change (M + gaussianRowMatrix x.1) * Oᵀ * (O * (M + gaussianRowMatrix x.1)ᵀ) +
    (x.2 : Matrix (Fin m) (Fin m) ℝ) = _
  calc
    _ = (M + gaussianRowMatrix x.1) * (Oᵀ * O) *
        (M + gaussianRowMatrix x.1)ᵀ + (x.2 : Matrix (Fin m) (Fin m) ℝ) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hOO, Matrix.mul_one]; rfl

/-- Spectral square root, proved by uniqueness of the positive square root. -/
theorem sqrt_spectral_matrix {q : ℕ} (O : Matrix (Fin q) (Fin q) ℝ)
    (hO : O * Oᵀ = 1) (lam : Fin q → ℝ) (hlam : ∀ i, 0 ≤ lam i) :
    CFC.sqrt (O * Matrix.diagonal lam * Oᵀ) =
      O * Matrix.diagonal (fun i => Real.sqrt (lam i)) * Oᵀ := by
  let D : Matrix (Fin q) (Fin q) ℝ := Matrix.diagonal (fun i => Real.sqrt (lam i))
  have hOO : Oᵀ * O = 1 := mul_eq_one_comm.mp hO
  have hD : D.PosSemidef := Matrix.PosSemidef.diagonal (fun i => Real.sqrt_nonneg (lam i))
  apply CFC.sqrt_unique
  · change O * D * Oᵀ * (O * D * Oᵀ) = O * Matrix.diagonal lam * Oᵀ
    have hDD : D * D = Matrix.diagonal lam := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      exact Real.mul_self_sqrt (hlam i)
    calc
      O * D * Oᵀ * (O * D * Oᵀ) = O * D * (Oᵀ * O) * D * Oᵀ := by
        simp only [Matrix.mul_assoc]
      _ = O * (D * D) * Oᵀ := by rw [hOO, Matrix.mul_one, Matrix.mul_assoc O D D]
      _ = _ := by rw [hDD]
  · exact (show (O * D * Oᵀ).PosSemidef from by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        hD.mul_mul_conjTranspose_same O).nonneg

def spectralRegressionMean {q m : ℕ} (K : Matrix (Fin q) (Fin m) ℝ)
    (O : Matrix (Fin q) (Fin q) ℝ) (lam : Fin q → ℝ) : Matrix (Fin m) (Fin q) ℝ :=
  Kᵀ * O * Matrix.diagonal (fun i => Real.sqrt (lam i))

@[simp] theorem spectralRegressionMean_apply {q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (O : Matrix (Fin q) (Fin q) ℝ)
    (lam : Fin q → ℝ) (i : Fin m) (a : Fin q) :
    spectralRegressionMean K O lam i a = Real.sqrt (lam a) * (Oᵀ * K) a i := by
  change (Kᵀ * O * Matrix.diagonal (fun j => Real.sqrt (lam j))) i a = _
  rw [Matrix.mul_diagonal]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

@[fun_prop] theorem measurable_spectralRegressionMean {q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) :
    Measurable (fun y : (Fin q → ℝ) × Matrix (Fin q) (Fin q) ℝ =>
      spectralRegressionMean K y.2 y.1) := by
  apply Matrix.measurable_iff.mpr
  intro i j
  simp only [spectralRegressionMean_apply, Matrix.mul_apply, Matrix.transpose_apply]
  fun_prop

/-- Exact source-law identity for the conditional remaining block in spectral
coordinates. It includes its independent residual Wishart matrix. -/
theorem map_regressionTail_spectral {q m : ℕ} (n : ℝ)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosSemidef)
    (K : Matrix (Fin q) (Fin m) ℝ) (O : Matrix (Fin q) (Fin q) ℝ)
    (hO : O * Oᵀ = 1) (lam : Fin q → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (S : SymmetricMatrix q)
    (hS : (S : Matrix (Fin q) (Fin q) ℝ) = O * Matrix.diagonal lam * Oᵀ) :
    (regressionNoiseMeasure n q m C).map
        (fun x => principalSymmetricBlock (Fin.natAdd q)
          (regressionReconstruction K (S, x))) =
      (regressionNoiseMeasure n q m C).map
        (regressionGramWithMean (spectralRegressionMean K O lam)) := by
  simp_rw [regressionReconstruction_trailing]
  have hmean : Kᵀ * CFC.sqrt (S : Matrix (Fin q) (Fin q) ℝ) =
      spectralRegressionMean K O lam * Oᵀ := by
    rw [hS, sqrt_spectral_matrix O hO lam hlam]
    simp only [spectralRegressionMean, Matrix.mul_assoc]
  rw [hmean]
  have hrotate := measurePreserving_regressionNoiseRotation (m := m) n hC O hO
  conv_lhs => rw [← hrotate.map_eq]
  rw [Measure.map_map (measurable_regressionGramWithMean _) hrotate.measurable]
  congr 1
  funext x
  exact regressionGramWithMean_rotation (spectralRegressionMean K O lam) O hO x

end Wishart
end
end CanonicalSource32

section CanonicalSource33
/- Source: Wishart/StochasticMonotonicity.lean -/



/-!
# Ordered laws and noncentral Gaussian squares

The stochastic order is the usual reversed order of distribution functions,
not the pointwise order on measures. Quantile couplings give both the finite
product construction and comparison of expectations of monotone functions.
The Gaussian-square theorem is the scalar input to manuscript Lemma 3.2.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open scoped NNReal ENNReal BigOperators

namespace WishartVerification

theorem integral_le_of_cdf_le {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : ℝ → ℝ} (hf : Monotone f)
    (hμ : Integrable f μ) (hν : Integrable f ν)
    (horder : ∀ x, cdf ν x ≤ cdf μ x) :
    ∫ x, f x ∂μ ≤ ∫ x, f x ∂ν := by
  let π := μ.quantileCoupling ν
  have hπ := μ.isCoupling_quantileCoupling ν
  have hle : (fun z : ℝ × ℝ => f z.1) ≤ᵐ[π] fun z => f z.2 := by
    filter_upwards [μ.ae_fst_le_snd_quantileCoupling ν horder] with z hz
    exact hf hz
  have h := integral_mono_ae (hπ.integrable_comp_fst hμ)
    (hπ.integrable_comp_snd hν) hle
  simpa only [hπ.integral_comp_fst hμ.aestronglyMeasurable,
    hπ.integral_comp_snd hν.aestronglyMeasurable] using h

theorem integral_lt_of_cdf_le_of_ne {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : ℝ → ℝ} (hf : StrictMono f)
    (hμ : Integrable f μ) (hν : Integrable f ν)
    (horder : ∀ x, cdf ν x ≤ cdf μ x) (hne : μ ≠ ν) :
    ∫ x, f x ∂μ < ∫ x, f x ∂ν := by
  have hle := integral_le_of_cdf_le hf.monotone hμ hν horder
  refine lt_of_le_of_ne hle ?_
  intro heq
  let π := μ.quantileCoupling ν
  have hπ := μ.isCoupling_quantileCoupling ν
  have hfg : (fun z : ℝ × ℝ => f z.1) ≤ᵐ[π] fun z => f z.2 := by
    filter_upwards [μ.ae_fst_le_snd_quantileCoupling ν horder] with z hz
    exact hf.monotone hz
  have hint : ∫ z, f z.1 ∂π = ∫ z, f z.2 ∂π := by
    rw [hπ.integral_comp_fst hμ.aestronglyMeasurable,
      hπ.integral_comp_snd hν.aestronglyMeasurable]
    exact heq
  have heqae := (integral_eq_iff_of_ae_le (hπ.integrable_comp_fst hμ)
    (hπ.integrable_comp_snd hν) hfg).mp hint
  have hcoord : Prod.fst =ᵐ[π] Prod.snd := heqae.mono fun z hz => hf.injective hz
  apply hne
  calc
    μ = π.map Prod.fst := hπ.measurePreserving_fst.map_eq.symm
    _ = π.map Prod.snd := Measure.map_congr hcoord
    _ = ν := hπ.measurePreserving_snd.map_eq

theorem noncentralChiSquaredMeasure_ne_of_noncentrality_ne
    {k : ℝ} (hk : 0 ≤ k) {a b : ℝ≥0} (hab : a ≠ b) :
    noncentralChiSquaredMeasure k a ≠ noncentralChiSquaredMeasure k b := by
  intro heq
  have h := congrArg (fun μ : Measure ℝ => ∫ x, x ∂μ) heq
  rw [integral_id_noncentralChiSquaredMeasure hk,
    integral_id_noncentralChiSquaredMeasure hk] at h
  exact hab (NNReal.coe_injective (add_left_cancel h))

theorem integral_lt_of_cdf_le_on_support {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : ℝ → ℝ} {s : Set ℝ} (hf : StrictMonoOn f s)
    (hsμ : ∀ᵐ x ∂μ, x ∈ s) (hsν : ∀ᵐ x ∂ν, x ∈ s)
    (hμ : Integrable f μ) (hν : Integrable f ν)
    (horder : ∀ x, cdf ν x ≤ cdf μ x) (hne : μ ≠ ν) :
    ∫ x, f x ∂μ < ∫ x, f x ∂ν := by
  let π := μ.quantileCoupling ν
  have hπ := μ.isCoupling_quantileCoupling ν
  have hfst : ∀ᵐ z ∂π, z.1 ∈ s :=
    hπ.measurePreserving_fst.quasiMeasurePreserving.ae hsμ
  have hsnd : ∀ᵐ z ∂π, z.2 ∈ s :=
    hπ.measurePreserving_snd.quasiMeasurePreserving.ae hsν
  have hfg : (fun z : ℝ × ℝ => f z.1) ≤ᵐ[π] fun z => f z.2 := by
    filter_upwards [μ.ae_fst_le_snd_quantileCoupling ν horder, hfst, hsnd]
      with z hz hzfst hzsnd
    exact hf.monotoneOn hzfst hzsnd hz
  have hle := integral_mono_ae (hπ.integrable_comp_fst hμ)
    (hπ.integrable_comp_snd hν) hfg
  rw [hπ.integral_comp_fst hμ.aestronglyMeasurable,
    hπ.integral_comp_snd hν.aestronglyMeasurable] at hle
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hint : ∫ z, f z.1 ∂π = ∫ z, f z.2 ∂π := by
    rw [hπ.integral_comp_fst hμ.aestronglyMeasurable,
      hπ.integral_comp_snd hν.aestronglyMeasurable]
    exact heq
  have heqae := (integral_eq_iff_of_ae_le (hπ.integrable_comp_fst hμ)
    (hπ.integrable_comp_snd hν) hfg).mp hint
  have hcoord : Prod.fst =ᵐ[π] Prod.snd := by
    filter_upwards [heqae, hfst, hsnd] with z hz hzfst hzsnd
    exact hf.injOn hzfst hzsnd hz
  exact hne (hπ.measurePreserving_fst.map_eq.symm.trans
    ((Measure.map_congr hcoord).trans hπ.measurePreserving_snd.map_eq))

theorem gaussian_shift_square_law (t c : ℝ) :
    (gaussianReal 0 1).map (fun x : ℝ => (x + Real.sqrt t * c) ^ 2) =
      noncentralChiSquaredMeasure 1 (‖Real.sqrt t * c‖₊ ^ 2) := by
  have hcomp : (fun x : ℝ => (x + Real.sqrt t * c) ^ 2) =
      (fun x : ℝ => x ^ 2) ∘ (fun x : ℝ => x + Real.sqrt t * c) := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
    gaussianReal_map_add_const, zero_add, gaussianReal_map_sq_noncentral]

theorem cdf_gaussian_shift_square_antitone {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (c x : ℝ) :
    cdf ((gaussianReal 0 1).map (fun z : ℝ => (z + Real.sqrt t * c) ^ 2)) x ≤
      cdf ((gaussianReal 0 1).map (fun z : ℝ => (z + Real.sqrt s * c) ^ 2)) x := by
  rw [gaussian_shift_square_law, gaussian_shift_square_law]
  apply cdf_noncentralChiSquaredMeasure_le (by norm_num) le_rfl
  apply NNReal.coe_le_coe.mp
  simp only [NNReal.coe_pow, coe_nnnorm, Real.norm_eq_abs, sq_abs, mul_pow]
  rw [Real.sq_sqrt hs, Real.sq_sqrt (hs.trans hst)]
  exact mul_le_mul_of_nonneg_right hst (sq_nonneg c)

theorem cdf_map_pi_le_of_coordinatewise_order
    {ι : Type*} [Fintype ι] (μ ν : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    (horder : ∀ i x, cdf (ν i) x ≤ cdf (μ i) x)
    {f g : (ι → ℝ) → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfg : ∀ x y, x ≤ y → f x ≤ g y) (a : ℝ) :
    cdf ((Measure.pi ν).map g) a ≤ cdf ((Measure.pi μ).map f) a := by
  classical
  let π : ι → Measure (ℝ × ℝ) := fun i => (μ i).quantileCoupling (ν i)
  have hπ (i : ι) : IsCoupling (π i) (μ i) (ν i) :=
    (μ i).isCoupling_quantileCoupling (ν i)
  letI (i : ι) : IsProbabilityMeasure (π i) := (hπ i).isProbabilityMeasure
  let P := Measure.pi π
  have hfst : HasLaw (fun z : ι → ℝ × ℝ => fun i => (z i).1)
      (Measure.pi μ) P := by
    refine ⟨(measurable_pi_iff.mpr
      (fun i => measurable_fst.comp (measurable_pi_apply i))).aemeasurable, ?_⟩
    rw [Measure.pi_map_pi (fun _ => measurable_fst.aemeasurable)]
    congr 1
    funext i
    exact (hπ i).measurePreserving_fst.map_eq
  have hsnd : HasLaw (fun z : ι → ℝ × ℝ => fun i => (z i).2)
      (Measure.pi ν) P := by
    refine ⟨(measurable_pi_iff.mpr
      (fun i => measurable_snd.comp (measurable_pi_apply i))).aemeasurable, ?_⟩
    rw [Measure.pi_map_pi (fun _ => measurable_snd.aemeasurable)]
    congr 1
    funext i
    exact (hπ i).measurePreserving_snd.map_eq
  have hF := (hasLaw_map hf.aemeasurable).fun_comp hfst
  have hG := (hasLaw_map hg.aemeasurable).fun_comp hsnd
  apply hF.cdf_le_of_ae_le hG _ a
  have hcoord : ∀ i, ∀ᵐ z ∂P, (z i).1 ≤ (z i).2 := by
    intro i
    exact (Measure.quasiMeasurePreserving_eval π i).ae
      ((μ i).ae_fst_le_snd_quantileCoupling (ν i) (horder i))
  filter_upwards [ae_all_iff.mpr hcoord] with z hz
  exact hfg _ _ hz

theorem cdf_weighted_gaussian_shift_squares_antitone
    {ι : Type*} [Fintype ι] (w c : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) {d s t : ℝ} (hd : 0 ≤ d)
    (hs : 0 ≤ s) (hst : s ≤ t) (a : ℝ) :
    cdf ((Measure.pi (fun _ : ι => gaussianReal 0 1)).map
      (fun z : ι → ℝ => ∑ i, w i * (z i + Real.sqrt t * c i) ^ 2 + t * d)) a ≤
    cdf ((Measure.pi (fun _ : ι => gaussianReal 0 1)).map
      (fun z : ι → ℝ => ∑ i, w i * (z i + Real.sqrt s * c i) ^ 2 + s * d)) a := by
  classical
  let law (r : ℝ) (i : ι) : Measure ℝ :=
    (gaussianReal 0 1).map (fun z : ℝ => (z + Real.sqrt r * c i) ^ 2)
  let F (r : ℝ) (x : ι → ℝ) := ∑ i, w i * x i + r * d
  have hmap (r : ℝ) :
      (Measure.pi (fun _ : ι => gaussianReal 0 1)).map
        (fun z : ι → ℝ => ∑ i, w i * (z i + Real.sqrt r * c i) ^ 2 + r * d) =
      (Measure.pi (law r)).map (F r) := by
    rw [← Measure.pi_map_pi (μ := fun _ : ι => gaussianReal 0 1)
      (f := fun i z => (z + Real.sqrt r * c i) ^ 2) (fun _ => by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [hmap, hmap]
  letI (r : ℝ) (i : ι) : IsProbabilityMeasure (law r i) := by
    dsimp [law]
    infer_instance
  apply cdf_map_pi_le_of_coordinatewise_order (law s) (law t)
    (fun i x => cdf_gaussian_shift_square_antitone hs hst (c i) x)
    (by dsimp [F]; fun_prop) (by dsimp [F]; fun_prop) _ a
  intro x y hxy
  exact add_le_add
    (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hxy i) (hw i))
    (mul_le_mul_of_nonneg_right hst hd)

/-- The diagonal-covariance version includes zero variances.  Their contribution
is the nonnegative deterministic term `t * ∑ dᵢ²` on the null coordinates. -/
theorem cdf_diagonal_gaussian_shift_norm_antitone
    {ι : Type*} [Fintype ι] (w d : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (a : ℝ) :
    cdf ((Measure.pi (fun _ : ι => gaussianReal 0 1)).map
      (fun z : ι → ℝ => ∑ i, (Real.sqrt (w i) * z i + Real.sqrt t * d i) ^ 2)) a ≤
    cdf ((Measure.pi (fun _ : ι => gaussianReal 0 1)).map
      (fun z : ι → ℝ => ∑ i, (Real.sqrt (w i) * z i + Real.sqrt s * d i) ^ 2)) a := by
  classical
  let c : ι → ℝ := fun i => d i / Real.sqrt (w i)
  let e : ℝ := ∑ i, if w i = 0 then (d i) ^ 2 else 0
  have he : 0 ≤ e := Finset.sum_nonneg fun i _ => by
    split_ifs <;> positivity
  have hsum (r : ℝ) (hr : 0 ≤ r) (z : ι → ℝ) :
      (∑ i, (Real.sqrt (w i) * z i + Real.sqrt r * d i) ^ 2) =
        ∑ i, w i * (z i + Real.sqrt r * c i) ^ 2 + r * e := by
    dsimp [e]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : w i = 0
    · simp [hi, mul_pow, Real.sq_sqrt hr]
    · have hwi : 0 < w i := lt_of_le_of_ne (hw i) (Ne.symm hi)
      have hroot : Real.sqrt (w i) ≠ 0 := (Real.sqrt_pos.2 hwi).ne'
      simp only [hi, ↓reduceIte, mul_zero, add_zero]
      dsimp [c]
      calc
        (Real.sqrt (w i) * z i + Real.sqrt r * d i) ^ 2 =
            (Real.sqrt (w i) * (z i + Real.sqrt r * (d i / Real.sqrt (w i)))) ^ 2 := by
          congr 1
          field_simp
        _ = w i * (z i + Real.sqrt r * (d i / Real.sqrt (w i))) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (hw i)]
  have hmap (r : ℝ) (hr : 0 ≤ r) :
      (Measure.pi (fun _ : ι => gaussianReal 0 1)).map
        (fun z : ι → ℝ => ∑ i, (Real.sqrt (w i) * z i + Real.sqrt r * d i) ^ 2) =
      (Measure.pi (fun _ : ι => gaussianReal 0 1)).map
        (fun z : ι → ℝ => ∑ i, w i * (z i + Real.sqrt r * c i) ^ 2 + r * e) := by
    congr 1
    funext z
    exact hsum r hr z
  rw [hmap t (hs.trans hst), hmap s hs]
  exact cdf_weighted_gaussian_shift_squares_antitone w c hw he hs hst a

theorem cdf_map_const_add_le_of_cdf_le {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (horder : ∀ x, cdf ν x ≤ cdf μ x) (c a : ℝ) :
    cdf (ν.map (fun x => c + x)) a ≤ cdf (μ.map (fun x => c + x)) a :=
  Measure.cdf_map_le_cdf_map_of_monotone
    (g := fun x => c + x) (fun _ _ h => by simpa [add_comm] using add_le_add_left h c) horder a

end WishartVerification
end
end CanonicalSource33

section CanonicalSource34
/- Source: Wishart/AdjugateRankOne.lean -/



/-!
# A rank-one determinant perturbation on the closed positive cone

The covariance and the background matrix in manuscript Lemma 3.2 may be
singular.  These lemmas retain that range.  The positive definite determinant
lemma is extended to the closed cone by adding `ε I` and taking `ε ↓ 0`.
-/

noncomputable section

open Matrix Filter Topology
open scoped BigOperators

namespace WishartVerification

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem adjugate_eq_det_smul_inv {A : Matrix ι ι ℝ} (hA : A.det ≠ 0) :
    A.adjugate = A.det • A⁻¹ := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv, smul_smul, mul_inv_cancel₀ hA, one_smul]

theorem adjugate_posDef {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    A.adjugate.PosDef := by
  rw [adjugate_eq_det_smul_inv hA.det_pos.ne']
  exact hA.inv.smul hA.det_pos

theorem det_add_vecMulVec_of_posDef {A : Matrix ι ι ℝ}
    (hA : A.PosDef) (u v : ι → ℝ) :
    (A + Matrix.vecMulVec u v).det = A.det + v ⬝ᵥ A.adjugate.mulVec u := by
  have h := Matrix.det_add_replicateCol_mul_replicateRow
    (ι := Unit) (isUnit_iff_ne_zero.mpr hA.det_pos.ne') u v
  have hrank : Matrix.replicateCol Unit u * Matrix.replicateRow Unit v =
      Matrix.vecMulVec u v := by
    ext i j
    simp [Matrix.mul_apply, Matrix.vecMulVec_apply]
  rw [hrank, Matrix.det_unique (n := Unit)] at h
  rw [adjugate_eq_det_smul_inv hA.det_pos.ne']
  simp only [Matrix.add_apply, Matrix.one_apply_eq] at h
  rw [h]
  rw [Matrix.mul_assoc]
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.mul_sum,
    Finset.sum_mul, mul_add, mul_assoc, mul_left_comm, mul_comm]

theorem posDef_add_epsilon_identity {A : Matrix ι ι ℝ}
    (hA : A.PosSemidef) {ε : ℝ} (hε : 0 < ε) :
    (A + ε • (1 : Matrix ι ι ℝ)).PosDef :=
  Matrix.PosDef.posSemidef_add hA (Matrix.PosDef.one.smul hε)

theorem tendsto_add_epsilon_identity (A : Matrix ι ι ℝ) :
    Tendsto (fun ε : ℝ => A + ε • (1 : Matrix ι ι ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 A) := by
  have hc : Continuous (fun ε : ℝ => A + ε • (1 : Matrix ι ι ℝ)) := by fun_prop
  simpa using (hc.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))

theorem adjugate_posSemidef {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    A.adjugate.PosSemidef := by
  apply Matrix.posSemidef_is_closed.mem_of_tendsto
    ((continuous_id.matrix_adjugate.tendsto A).comp (tendsto_add_epsilon_identity A))
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (adjugate_posDef (posDef_add_epsilon_identity hA hε)).posSemidef

theorem det_add_vecMulVec_of_posSemidef {A : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (u v : ι → ℝ) :
    (A + Matrix.vecMulVec u v).det = A.det + v ⬝ᵥ A.adjugate.mulVec u := by
  let f : Matrix ι ι ℝ → ℝ := fun B => (B + Matrix.vecMulVec u v).det
  let g : Matrix ι ι ℝ → ℝ := fun B => B.det + v ⬝ᵥ B.adjugate.mulVec u
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hclosed : IsClosed {B : Matrix ι ι ℝ | f B = g B} := isClosed_eq hf hg
  apply hclosed.mem_of_tendsto (tendsto_add_epsilon_identity A)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact det_add_vecMulVec_of_posDef (posDef_add_epsilon_identity hA hε) u v

theorem det_rankOne_shift_eq_quadratic {A : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (z v : ι → ℝ) (t : ℝ) :
    (A + Matrix.vecMulVec (z + Real.sqrt t • v) (z + Real.sqrt t • v)).det =
      A.det + (z + Real.sqrt t • v) ⬝ᵥ A.adjugate.mulVec (z + Real.sqrt t • v) :=
  det_add_vecMulVec_of_posSemidef hA _ _

end WishartVerification
end
end CanonicalSource34

section CanonicalSource35
/- Source: Wishart/GaussianQuadraticOrder.lean -/



/-!
# Gaussian shifts of positive quadratic forms

An orthonormal eigenbasis reduces the squared norm of a Gaussian with arbitrary
positive semidefinite covariance to independent one-dimensional shifted
squares.  In particular, no density or inverse of the covariance is used.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability Matrix
open scoped BigOperators RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace WishartVerification

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def eigenGaussianMatrix {C : Matrix ι ι ℝ} (hC : C.PosSemidef) : Matrix ι ι ℝ :=
  (hC.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ) *
    Matrix.diagonal (fun i => Real.sqrt (hC.isHermitian.eigenvalues i))

def eigenGaussianSample {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (z : ι → ℝ) : EuclideanSpace ℝ ι :=
  hC.isHermitian.eigenvectorBasis.repr.symm
    (WithLp.toLp 2 fun i => Real.sqrt (hC.isHermitian.eigenvalues i) * z i)

theorem eigenGaussianMatrix_covariance {C : Matrix ι ι ℝ} (hC : C.PosSemidef) :
    eigenGaussianMatrix hC * (eigenGaussianMatrix hC)ᵀ = C := by
  let U : Matrix ι ι ℝ := hC.isHermitian.eigenvectorUnitary
  let D : Matrix ι ι ℝ := Matrix.diagonal fun i => Real.sqrt (hC.isHermitian.eigenvalues i)
  have hDD : D * D = Matrix.diagonal hC.isHermitian.eigenvalues := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact (Real.mul_self_sqrt (hC.eigenvalues_nonneg i))
  have hspectral : C = U * Matrix.diagonal hC.isHermitian.eigenvalues * Uᵀ := by
    simpa [U, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      hC.isHermitian.spectral_theorem
  change U * D * (U * D)ᵀ = C
  rw [Matrix.transpose_mul, show Dᵀ = D by simp [D], Matrix.mul_assoc U D,
    ← Matrix.mul_assoc D D, hDD, ← Matrix.mul_assoc, ← hspectral]

theorem eigenGaussianSample_eq_matrix {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (z : ι → ℝ) :
    eigenGaussianSample hC z =
      (eigenGaussianMatrix hC).toEuclideanLin (WithLp.toLp 2 z) := by
  rw [eigenGaussianSample, ← hC.isHermitian.eigenvectorBasis.sum_repr_symm]
  apply PiLp.ext
  intro i
  simp [eigenGaussianMatrix, Matrix.toLpLin_apply, ← Matrix.mulVec_mulVec,
    Matrix.mulVec_diagonal, Matrix.mulVec, dotProduct,
    Matrix.IsHermitian.eigenvectorUnitary_apply, Matrix.diagonal_apply, mul_comm]

@[fun_prop] theorem measurable_eigenGaussianSample {C : Matrix ι ι ℝ}
    (hC : C.PosSemidef) : Measurable (eigenGaussianSample hC) := by
  unfold eigenGaussianSample
  fun_prop

theorem map_eigenGaussianSample {C : Matrix ι ι ℝ} (hC : C.PosSemidef) :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)).map (eigenGaussianSample hC) =
      multivariateGaussian 0 C := by
  have h := map_affine_multivariateGaussian (0 : EuclideanSpace ℝ ι)
    Matrix.PosSemidef.one (eigenGaussianMatrix hC) 0
  simp only [map_zero, add_zero, Matrix.mul_one, eigenGaussianMatrix_covariance hC] at h
  rw [multivariateGaussian_one_eq_map_pi, Measure.map_map (by fun_prop) (by fun_prop)] at h
  convert h using 1
  congr 1
  funext z
  exact eigenGaussianSample_eq_matrix hC z

theorem norm_eigenGaussianSample_shift_sq {C : Matrix ι ι ℝ}
    (hC : C.PosSemidef) (z : ι → ℝ) (v : EuclideanSpace ℝ ι) (r : ℝ) :
    ‖eigenGaussianSample hC z + Real.sqrt r • v‖ ^ 2 =
      ∑ i, (Real.sqrt (hC.isHermitian.eigenvalues i) * z i +
        Real.sqrt r * hC.isHermitian.eigenvectorBasis.repr v i) ^ 2 := by
  rw [← hC.isHermitian.eigenvectorBasis.repr.norm_map
    (eigenGaussianSample hC z + Real.sqrt r • v), EuclideanSpace.real_norm_sq_eq]
  simp [eigenGaussianSample, map_add, map_smul]

theorem cdf_gaussian_shift_norm_antitone {C : Matrix ι ι ℝ}
    (hC : C.PosSemidef) (v : EuclideanSpace ℝ ι)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (a : ℝ) :
    cdf ((multivariateGaussian 0 C).map
      (fun z => ‖z + Real.sqrt t • v‖ ^ 2)) a ≤
    cdf ((multivariateGaussian 0 C).map
      (fun z => ‖z + Real.sqrt s • v‖ ^ 2)) a := by
  rw [← map_eigenGaussianSample hC,
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  simpa only [Function.comp_def, norm_eigenGaussianSample_shift_sq] using
    cdf_diagonal_gaussian_shift_norm_antitone hC.isHermitian.eigenvalues
      (fun i => hC.isHermitian.eigenvectorBasis.repr v i)
      hC.eigenvalues_nonneg hs hst a

theorem norm_sqrt_toEuclideanLin_sq {A : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (x : EuclideanSpace ℝ ι) :
    ‖(CFC.sqrt A).toEuclideanLin x‖ ^ 2 = x.ofLp ⬝ᵥ A.mulVec x.ofLp := by
  have hsqrt : (CFC.sqrt A)ᴴ = CFC.sqrt A :=
    (Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg A)).isHermitian.eq
  have h := Matrix.inner_toEuclideanLin_toEuclideanLin (CFC.sqrt A)
    (1 : Matrix ι ι ℝ) x
  simpa [hsqrt, Matrix.mul_one, dotProduct_comm,
    CFC.sqrt_mul_sqrt_self A hA.nonneg, real_inner_self_eq_norm_sq,
    EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply] using h

theorem cdf_gaussian_shift_quadratic_antitone {A C : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hC : C.PosSemidef) (v : EuclideanSpace ℝ ι)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (a : ℝ) :
    cdf ((multivariateGaussian 0 C).map (fun z =>
      (z + Real.sqrt t • v).ofLp ⬝ᵥ A.mulVec (z + Real.sqrt t • v).ofLp)) a ≤
    cdf ((multivariateGaussian 0 C).map (fun z =>
      (z + Real.sqrt s • v).ofLp ⬝ᵥ A.mulVec (z + Real.sqrt s • v).ofLp)) a := by
  let L : Matrix ι ι ℝ := CFC.sqrt A
  let D : Matrix ι ι ℝ := L * C * Lᵀ
  have hD : D.PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hC.mul_mul_conjTranspose_same L
  have hmap : (multivariateGaussian 0 C).map L.toEuclideanLin =
      multivariateGaussian 0 D := by
    simpa [D] using map_affine_multivariateGaussian (0 : EuclideanSpace ℝ ι) hC L 0
  have h := cdf_gaussian_shift_norm_antitone hD (L.toEuclideanLin v) hs hst a
  rw [← hmap, Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)] at h
  simpa only [Function.comp_def, ← map_smul, ← map_add, L,
    norm_sqrt_toEuclideanLin_sq hA] using h

/-- Stochastic monotonicity in the full positive semidefinite parameter range
of manuscript Lemma 3.2.  Strict positive moments are proved separately. -/
theorem cdf_gaussian_shift_determinant_antitone {B C : Matrix ι ι ℝ}
    (hB : B.PosSemidef) (hC : C.PosSemidef) (v : EuclideanSpace ℝ ι)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (a : ℝ) :
    cdf ((multivariateGaussian 0 C).map (fun z =>
      (B + Matrix.vecMulVec (z + Real.sqrt t • v).ofLp
        (z + Real.sqrt t • v).ofLp).det)) a ≤
    cdf ((multivariateGaussian 0 C).map (fun z =>
      (B + Matrix.vecMulVec (z + Real.sqrt s • v).ofLp
        (z + Real.sqrt s • v).ofLp).det)) a := by
  let law (r : ℝ) := (multivariateGaussian 0 C).map (fun z =>
    (z + Real.sqrt r • v).ofLp ⬝ᵥ B.adjugate.mulVec (z + Real.sqrt r • v).ofLp)
  letI (r : ℝ) : IsProbabilityMeasure (law r) := by
    dsimp [law]
    infer_instance
  have hmap (r : ℝ) :
      (multivariateGaussian 0 C).map (fun z =>
        (B + Matrix.vecMulVec (z + Real.sqrt r • v).ofLp
          (z + Real.sqrt r • v).ofLp).det) =
      (law r).map (fun x => B.det + x) := by
    dsimp only [law]
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext z
    exact det_add_vecMulVec_of_posSemidef hB _ _
  rw [hmap t, hmap s]
  exact cdf_map_const_add_le_of_cdf_le
    (cdf_gaussian_shift_quadratic_antitone (adjugate_posSemidef hB) hC v hs hst)
    B.det a

end WishartVerification
end
end CanonicalSource35

section CanonicalSource36
/- Source: Wishart/GaussianDeterminantStrict.lean -/



/-!
# Finite and strictly increasing Gaussian determinant moments

The strictness argument compares first moments to show that the ordered laws
are different, and then applies the ordered coupling to the strictly increasing
power function on the nonnegative half-line.  No strict stochastic-order claim
at every threshold is required.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability Matrix
open scoped BigOperators RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace WishartVerification

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def rankOneDeterminant (B : Matrix ι ι ℝ) (v : EuclideanSpace ℝ ι) (t : ℝ)
    (z : EuclideanSpace ℝ ι) : ℝ :=
  (B + Matrix.vecMulVec (z + Real.sqrt t • v).ofLp
    (z + Real.sqrt t • v).ofLp).det

@[fun_prop] theorem measurable_rankOneDeterminant (B : Matrix ι ι ℝ)
    (v : EuclideanSpace ℝ ι) (t : ℝ) : Measurable (rankOneDeterminant B v t) := by
  unfold rankOneDeterminant
  fun_prop

theorem allFiniteMoments_gaussian_coordinate (m : EuclideanSpace ℝ ι)
    (C : Matrix ι ι ℝ) (i : ι) :
    HasAllFiniteMoments (fun z : EuclideanSpace ℝ ι => z i) (multivariateGaussian m C) := by
  intro p hp
  simpa only [id_eq, EuclideanSpace.coe_proj] using
    (IsGaussian.memLp_id (multivariateGaussian m C) p hp).continuousLinearMap_comp
      (𝕜 := ℝ) (EuclideanSpace.proj i)

theorem allFiniteMoments_gaussian_rankOneDeterminant
    (m : EuclideanSpace ℝ ι) (B C : Matrix ι ι ℝ)
    (v : EuclideanSpace ℝ ι) (t : ℝ) :
    HasAllFiniteMoments (rankOneDeterminant B v t) (multivariateGaussian m C) := by
  apply HasAllFiniteMoments.det
  intro i j
  exact (HasAllFiniteMoments.const (B i j)).add
    (((allFiniteMoments_gaussian_coordinate m C i).add
      (HasAllFiniteMoments.const (Real.sqrt t * v i))).mul
     ((allFiniteMoments_gaussian_coordinate m C j).add
      (HasAllFiniteMoments.const (Real.sqrt t * v j))))

theorem integrable_gaussian_rankOneDeterminant_rpow
    (m : EuclideanSpace ℝ ι) (B C : Matrix ι ι ℝ)
    (v : EuclideanSpace ℝ ι) (t : ℝ) {η : ℝ} (hη : 0 ≤ η) :
    Integrable (fun z => rankOneDeterminant B v t z ^ η) (multivariateGaussian m C) :=
  ((allFiniteMoments_gaussian_rankOneDeterminant m B C v t).rpow hη).integrable

theorem integral_norm_sq_multivariateGaussian (m : EuclideanSpace ℝ ι)
    {C : Matrix ι ι ℝ} (hC : C.PosSemidef) :
    ∫ z, ‖z‖ ^ 2 ∂multivariateGaussian m C = ‖m‖ ^ 2 + C.trace := by
  rw [integral_norm_sq_eq_norm_integral_sq_add_trace_covMatrix _ IsGaussian.memLp_two_id,
    integral_id_multivariateGaussian, covMatrix_multivariateGaussian m hC]

theorem integral_gaussian_shift_norm_sq {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (v : EuclideanSpace ℝ ι) {t : ℝ} (ht : 0 ≤ t) :
    ∫ z, ‖z + Real.sqrt t • v‖ ^ 2 ∂multivariateGaussian 0 C =
      t * ‖v‖ ^ 2 + C.trace := by
  have hmap : (multivariateGaussian 0 C).map (fun z => z + Real.sqrt t • v) =
      multivariateGaussian (Real.sqrt t • v) C := by
    simpa [add_comm] using
      map_add_smul_multivariateGaussian (0 : EuclideanSpace ℝ ι) hC
        (Real.sqrt t • v) 1
  rw [← integral_map (φ := fun z : EuclideanSpace ℝ ι => z + Real.sqrt t • v)
    (f := fun y : EuclideanSpace ℝ ι => ‖y‖ ^ 2) (by fun_prop) (by fun_prop), hmap,
    integral_norm_sq_multivariateGaussian _ hC]
  simp [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt ht]

theorem rankOneDeterminant_nonneg {B : Matrix ι ι ℝ} (hB : B.PosSemidef)
    (v : EuclideanSpace ℝ ι) (t : ℝ) (z : EuclideanSpace ℝ ι) :
    0 ≤ rankOneDeterminant B v t z := by
  rw [rankOneDeterminant, det_add_vecMulVec_of_posSemidef hB]
  exact add_nonneg hB.det_nonneg (by
    simpa using (adjugate_posSemidef hB).dotProduct_mulVec_nonneg
      (z + Real.sqrt t • v).ofLp)

theorem integral_gaussian_rankOneDeterminant {B C : Matrix ι ι ℝ}
    (hB : B.PosSemidef) (hC : C.PosSemidef) (v : EuclideanSpace ℝ ι)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫ z, rankOneDeterminant B v t z ∂multivariateGaussian 0 C =
      B.det + t * (v.ofLp ⬝ᵥ B.adjugate.mulVec v.ofLp) +
        (CFC.sqrt B.adjugate * C * (CFC.sqrt B.adjugate)ᵀ).trace := by
  let L : Matrix ι ι ℝ := CFC.sqrt B.adjugate
  let D : Matrix ι ι ℝ := L * C * Lᵀ
  have hD : D.PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hC.mul_mul_conjTranspose_same L
  have hmap : (multivariateGaussian 0 C).map L.toEuclideanLin =
      multivariateGaussian 0 D := by
    simpa [D] using map_affine_multivariateGaussian (0 : EuclideanSpace ℝ ι) hC L 0
  have hquad : Integrable (fun z : EuclideanSpace ℝ ι =>
      ‖L.toEuclideanLin z + Real.sqrt t • L.toEuclideanLin v‖ ^ 2)
      (multivariateGaussian 0 C) := by
    have hdet := (allFiniteMoments_gaussian_rankOneDeterminant 0 B C v t).integrable
    have h := hdet.sub (integrable_const B.det)
    convert h using 1
    funext z
    change ‖L.toEuclideanLin z + Real.sqrt t • L.toEuclideanLin v‖ ^ 2 =
      rankOneDeterminant B v t z - B.det
    rw [← map_smul, ← map_add, norm_sqrt_toEuclideanLin_sq (adjugate_posSemidef hB),
      rankOneDeterminant, det_add_vecMulVec_of_posSemidef hB]
    ring
  have hfun : rankOneDeterminant B v t = fun z : EuclideanSpace ℝ ι =>
      B.det + ‖L.toEuclideanLin z + Real.sqrt t • L.toEuclideanLin v‖ ^ 2 := by
    funext z
    rw [← map_smul, ← map_add, norm_sqrt_toEuclideanLin_sq (adjugate_posSemidef hB),
      rankOneDeterminant, det_add_vecMulVec_of_posSemidef hB]
  rw [hfun, integral_add (integrable_const _) hquad, integral_const]
  simp only [probReal_univ, one_smul]
  rw [← integral_map (φ := L.toEuclideanLin)
    (f := fun y : EuclideanSpace ℝ ι => ‖y + Real.sqrt t • L.toEuclideanLin v‖ ^ 2)
    (by fun_prop) (by fun_prop), hmap,
    integral_gaussian_shift_norm_sq hD _ ht,
    norm_sqrt_toEuclideanLin_sq (adjugate_posSemidef hB)]
  ring

theorem gaussian_rankOneDeterminant_laws_ne {B C : Matrix ι ι ℝ}
    (hB : B.PosDef) (hC : C.PosSemidef) {v : EuclideanSpace ℝ ι} (hv : v ≠ 0)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    (multivariateGaussian 0 C).map (rankOneDeterminant B v s) ≠
      (multivariateGaussian 0 C).map (rankOneDeterminant B v t) := by
  intro heq
  have hm := congrArg (fun μ : Measure ℝ => ∫ x, x ∂μ) heq
  rw [integral_map (by fun_prop) (by fun_prop),
    integral_map (by fun_prop) (by fun_prop)] at hm
  try simp only [id_eq] at hm
  rw [integral_gaussian_rankOneDeterminant hB.posSemidef hC v hs,
    integral_gaussian_rankOneDeterminant hB.posSemidef hC v (hs.trans hst.le)] at hm
  have hpos : 0 < v.ofLp ⬝ᵥ B.adjugate.mulVec v.ofLp := by
    simpa using (adjugate_posDef hB).dotProduct_mulVec_pos
      ((WithLp.ofLp_eq_zero 2).not.mpr hv)
  nlinarith

/-- The strictly increasing positive moments assertion of manuscript Lemma 3.2.
The statement even permits a singular covariance; the background is positive
definite and the shift direction is nonzero. -/
theorem integral_gaussian_rankOneDeterminant_rpow_strictMono
    {B C : Matrix ι ι ℝ} (hB : B.PosDef) (hC : C.PosSemidef)
    {v : EuclideanSpace ℝ ι} (hv : v ≠ 0) {η : ℝ} (hη : 0 < η) :
    StrictMonoOn (fun t : ℝ => ∫ z, rankOneDeterminant B v t z ^ η
      ∂multivariateGaussian 0 C) (Set.Ici 0) := by
  intro s hs t ht hst
  let law (r : ℝ) := (multivariateGaussian 0 C).map (rankOneDeterminant B v r)
  letI (r : ℝ) : IsProbabilityMeasure (law r) :=
    by infer_instance
  have hsupport (r : ℝ) : ∀ᵐ x ∂law r, x ∈ Set.Ici 0 := by
    change ∀ᵐ x ∂(multivariateGaussian 0 C).map (rankOneDeterminant B v r), (0 : ℝ) ≤ x
    rw [ae_map_iff (by fun_prop) measurableSet_Ici]
    exact Filter.Eventually.of_forall (rankOneDeterminant_nonneg hB.posSemidef v r)
  have hint (r : ℝ) : Integrable (fun x : ℝ => x ^ η) (law r) :=
    (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
      (integrable_gaussian_rankOneDeterminant_rpow 0 B C v r hη.le)
  have hlt := integral_lt_of_cdf_le_on_support
    (Real.strictMonoOn_rpow_Ici_of_exponent_pos hη)
    (hsupport s) (hsupport t) (hint s) (hint t)
    (cdf_gaussian_shift_determinant_antitone hB.posSemidef hC v hs hst.le)
    (gaussian_rankOneDeterminant_laws_ne hB hC hv hs hst)
  have he (r : ℝ) : (∫ x, x ^ η ∂law r) =
      ∫ z, rankOneDeterminant B v r z ^ η ∂multivariateGaussian 0 C :=
    integral_map (by fun_prop) (by fun_prop)
  rw [he s, he t] at hlt
  exact hlt

end WishartVerification
end
end CanonicalSource36

section CanonicalSource37
/- Source: Wishart/Association.lean -/



open scoped Classical

/-!
# One-dimensional association

The one-dimensional base case used in Lemma 2.1 of
`The Wishart product inequality and spectral correlation`.

This file proves an integral identity and the Chebyshev association inequality
for arbitrary probability measures on linearly ordered measurable spaces.
No Wishart law or multidimensional association theorem is assumed or claimed.
-/

open MeasureTheory

namespace WishartVerification

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable [IsProbabilityMeasure μ] {f g : Ω → ℝ}

/-- Integrability of one section of the covariance kernel. -/
theorem integrable_covariance_kernel (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : Integrable (fun x ↦ f x * g x) μ) (x : Ω) :
    Integrable (fun y ↦ (f x - f y) * (g x - g y)) μ := by
  have heq : (fun y ↦ (f x - f y) * (g x - g y)) =
      fun y ↦ ((f x * g x - f x * g y) - f y * g x) + f y * g y := by
    funext y
    ring
  rw [heq]
  exact (((integrable_const _).sub (hg.const_mul _)).sub (hf.mul_const _)).add hfg

/-- Integrating the two-point covariance kernel in its second argument. -/
theorem integral_covariance_kernel (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : Integrable (fun x ↦ f x * g x) μ) (x : Ω) :
    (∫ y, (f x - f y) * (g x - g y) ∂μ) =
      f x * g x - f x * (∫ y, g y ∂μ) - (∫ y, f y ∂μ) * g x +
        ∫ y, f y * g y ∂μ := by
  have heq : (fun y ↦ (f x - f y) * (g x - g y)) =
      fun y ↦ ((f x * g x - f x * g y) - f y * g x) + f y * g y := by
    funext y
    ring
  rw [heq, integral_add, integral_sub, integral_sub]
  · simp only [integral_const, probReal_univ, one_smul, integral_const_mul,
      integral_mul_const]
  · exact integrable_const _
  · exact hg.const_mul _
  · exact (integrable_const _).sub (hg.const_mul _)
  · exact hf.mul_const _
  · exact ((integrable_const _).sub (hg.const_mul _)).sub (hf.mul_const _)
  · exact hfg

/-- The covariance identity used at the start of Lemma 2.1.  The left-hand side
is written as an iterated integral, so that no independence representation needs
to be chosen. -/
theorem covariance_kernel_identity (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : Integrable (fun x ↦ f x * g x) μ) :
    (∫ x, ∫ y, (f x - f y) * (g x - g y) ∂μ ∂μ) =
      2 * ((∫ x, f x * g x ∂μ) - (∫ x, f x ∂μ) * (∫ x, g x ∂μ)) := by
  simp_rw [integral_covariance_kernel hf hg hfg]
  rw [integral_add, integral_sub, integral_sub]
  · simp only [integral_const, probReal_univ, one_smul, integral_const_mul,
      integral_mul_const]
    ring
  · exact hfg
  · exact hf.mul_const _
  · exact hfg.sub (hf.mul_const _)
  · exact hg.const_mul _
  · exact (hfg.sub (hf.mul_const _)).sub (hg.const_mul _)
  · exact integrable_const _

/-- Integrability of the first integral in the covariance identity. -/
theorem integrable_integral_covariance_kernel
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : Integrable (fun x ↦ f x * g x) μ) :
    Integrable (fun x ↦ ∫ y, (f x - f y) * (g x - g y) ∂μ) μ := by
  simp_rw [integral_covariance_kernel hf hg hfg]
  exact (((hfg.sub (hf.mul_const _)).sub (hg.const_mul _)).add (integrable_const _))

/-- The integral Chebyshev inequality for comonotone functions.  It is stronger
than the monotone specialization below and requires only the integrability
actually used by the identity. -/
theorem integral_mul_ge_mul_integral_of_comonotone
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : Integrable (fun x ↦ f x * g x) μ)
    (hmono : ∀ x y, 0 ≤ (f x - f y) * (g x - g y)) :
    (∫ x, f x ∂μ) * (∫ x, g x ∂μ) ≤ ∫ x, f x * g x ∂μ := by
  have hnonneg : 0 ≤ ∫ x, ∫ y, (f x - f y) * (g x - g y) ∂μ ∂μ :=
    integral_nonneg fun x ↦ integral_nonneg fun y ↦ hmono x y
  rw [covariance_kernel_identity hf hg hfg] at hnonneg
  linarith

/-- Every probability law on a linearly ordered measurable space is associated
for integrable monotone pairs with an integrable product. -/
theorem integral_mul_ge_mul_integral [LinearOrder Ω]
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : Integrable (fun x ↦ f x * g x) μ)
    (hfmono : Monotone f) (hgmono : Monotone g) :
    (∫ x, f x ∂μ) * (∫ x, g x ∂μ) ≤ ∫ x, f x * g x ∂μ := by
  apply integral_mul_ge_mul_integral_of_comonotone hf hg hfg
  intro x y
  rcases le_total x y with h | h
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hfmono h))
      (sub_nonpos.mpr (hgmono h))
  · exact mul_nonneg (sub_nonneg.mpr (hfmono h)) (sub_nonneg.mpr (hgmono h))

/-- The same inequality as nonnegativity of covariance, with precisely the
finite-second-moment hypotheses used for strictness in Lemma 2.1. -/
theorem covariance_nonneg [LinearOrder Ω]
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hfmono : Monotone f) (hgmono : Monotone g) :
    0 ≤ ProbabilityTheory.covariance f g μ := by
  rw [ProbabilityTheory.covariance_eq_sub hf hg]
  exact sub_nonneg.mpr (integral_mul_ge_mul_integral
    (hf.integrable (by norm_num)) (hg.integrable (by norm_num))
    (hf.integrable_mul hg) hfmono hgmono)

omit [MeasurableSpace Ω] in
/-- Strict monotonicity makes the covariance kernel positive off the diagonal. -/
theorem covariance_kernel_pos [LinearOrder Ω]
    (hfmono : StrictMono f) (hgmono : StrictMono g) {x y : Ω} (hxy : x ≠ y) :
    0 < (f x - f y) * (g x - g y) := by
  rcases lt_or_gt_of_ne hxy with h | h
  · exact mul_pos_of_neg_of_neg (sub_neg.mpr (hfmono h)) (sub_neg.mpr (hgmono h))
  · exact mul_pos (sub_pos.mpr (hfmono h)) (sub_pos.mpr (hgmono h))

/-- Strict Chebyshev association for a probability measure without point atoms.
This is the strict one-dimensional assertion needed for the positive eigenvalue
densities in the manuscript. -/
theorem integral_mul_gt_mul_integral [LinearOrder Ω] [MeasurableSingletonClass Ω]
    [NullSingletonClass μ]
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : Integrable (fun x ↦ f x * g x) μ)
    (hfmono : StrictMono f) (hgmono : StrictMono g) :
    (∫ x, f x ∂μ) * (∫ x, g x ∂μ) < ∫ x, f x * g x ∂μ := by
  have hinner : ∀ x, 0 < ∫ y, (f x - f y) * (g x - g y) ∂μ := by
    intro x
    have hnonneg : ∀ y, 0 ≤ (f x - f y) * (g x - g y) := by
      intro y
      by_cases hxy : x = y
      · simp [hxy]
      · exact (covariance_kernel_pos hfmono hgmono hxy).le
    rw [integral_pos_iff_support_of_nonneg hnonneg
      (integrable_covariance_kernel hf hg hfg x)]
    have hsupp : Function.support (fun y ↦ (f x - f y) * (g x - g y)) =
        ({x} : Set Ω)ᶜ := by
      ext y
      simp only [Function.mem_support, ne_eq, mul_eq_zero, sub_eq_zero,
        hfmono.injective.eq_iff, hgmono.injective.eq_iff, or_self, Set.mem_compl_iff,
        Set.mem_singleton_iff, ne_comm]
    rw [hsupp, measure_compl (measurableSet_singleton x) (by simp)]
    simp
  have houter : 0 < ∫ x, ∫ y, (f x - f y) * (g x - g y) ∂μ ∂μ := by
    rw [integral_pos_iff_support_of_nonneg (fun x ↦ (hinner x).le)
      (integrable_integral_covariance_kernel hf hg hfg)]
    have hsupp : Function.support (fun x ↦ ∫ y, (f x - f y) * (g x - g y) ∂μ) =
        Set.univ := by
      ext x
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact (hinner x).ne'
    simp [hsupp]
  rw [covariance_kernel_identity hf hg hfg] at houter
  linarith

/-- Strict covariance form with the finite-second-moment hypotheses appearing
in Lemma 2.1. -/
theorem covariance_pos [LinearOrder Ω] [MeasurableSingletonClass Ω]
    [NullSingletonClass μ]
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hfmono : StrictMono f) (hgmono : StrictMono g) :
    0 < ProbabilityTheory.covariance f g μ := by
  rw [ProbabilityTheory.covariance_eq_sub hf hg]
  exact sub_pos.mpr (integral_mul_gt_mul_integral
    (hf.integrable (by norm_num)) (hg.integrable (by norm_num))
    (hf.integrable_mul hg) hfmono hgmono)

end WishartVerification
end CanonicalSource37

section CanonicalSource38
/- Source: Wishart/AssociationAE.lean -/



open scoped Classical

/-!
# Association on a set of full probability

Conditional density normalizers and conditional moments need only be finite
almost everywhere. These variants of the one-dimensional covariance identity
allow a common full-measure set of admissible conditioning parameters.
-/

open MeasureTheory

namespace WishartVerification

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable [IsProbabilityMeasure μ] {f g : Ω → ℝ}

theorem integral_mul_ge_mul_integral_of_comonotone_ae
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : Integrable (fun x ↦ f x * g x) μ)
    (hmono : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, 0 ≤ (f x - f y) * (g x - g y)) :
    (∫ x, f x ∂μ) * (∫ x, g x ∂μ) ≤ ∫ x, f x * g x ∂μ := by
  have hnonneg : 0 ≤ ∫ x, ∫ y, (f x - f y) * (g x - g y) ∂μ ∂μ :=
    integral_nonneg_of_ae (hmono.mono fun x hx ↦ integral_nonneg_of_ae hx)
  rw [covariance_kernel_identity hf hg hfg] at hnonneg
  linarith

theorem integral_pos_of_pos_ae {h : Ω → ℝ} (hh : Integrable h μ)
    (hpos : ∀ᵐ x ∂μ, 0 < h x) : 0 < ∫ x, h x ∂μ := by
  rw [integral_pos_iff_support_of_nonneg_ae (hpos.mono fun _ hx ↦ hx.le) hh]
  have hsupp : Function.support h =ᵐ[μ] Set.univ := by
    filter_upwards [hpos] with x hx
    simp [Function.mem_support, hx.ne']
  rw [measure_congr hsupp, measure_univ]
  exact zero_lt_one

theorem integral_mul_gt_mul_integral_of_strict_comonotone_ae
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : Integrable (fun x ↦ f x * g x) μ)
    (hmono : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, 0 < (f x - f y) * (g x - g y)) :
    (∫ x, f x ∂μ) * (∫ x, g x ∂μ) < ∫ x, f x * g x ∂μ := by
  have hinner : ∀ᵐ x ∂μ, 0 < ∫ y, (f x - f y) * (g x - g y) ∂μ :=
    hmono.mono fun x hx ↦ integral_pos_of_pos_ae (integrable_covariance_kernel hf hg hfg x) hx
  have houter := integral_pos_of_pos_ae (integrable_integral_covariance_kernel hf hg hfg) hinner
  rw [covariance_kernel_identity hf hg hfg] at houter
  linarith

/-- The weak scalar inequality holds if both functions increase on one common
set of full probability. -/
theorem integral_mul_ge_mul_integral_of_monotoneOn_ae [LinearOrder Ω]
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : Integrable (fun x ↦ f x * g x) μ)
    (s : Set Ω) (hs : ∀ᵐ x ∂μ, x ∈ s)
    (hfm : MonotoneOn f s) (hgm : MonotoneOn g s) :
    (∫ x, f x ∂μ) * (∫ x, g x ∂μ) ≤ ∫ x, f x * g x ∂μ := by
  apply integral_mul_ge_mul_integral_of_comonotone_ae hf hg hfg
  filter_upwards [hs] with x hx
  filter_upwards [hs] with y hy
  rcases le_total x y with hxy | hyx
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hfm hx hy hxy))
      (sub_nonpos.mpr (hgm hx hy hxy))
  · exact mul_nonneg (sub_nonneg.mpr (hfm hy hx hyx))
      (sub_nonneg.mpr (hgm hy hx hyx))

/-- Strictness on a full-probability parameter set suffices. The atomlessness
hypothesis is exactly what excludes coinciding independent parameters. -/
theorem integral_mul_gt_mul_integral_of_strictMonoOn_ae [LinearOrder Ω]
    [NullSingletonClass μ]
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : Integrable (fun x ↦ f x * g x) μ)
    (s : Set Ω) (hs : ∀ᵐ x ∂μ, x ∈ s)
    (hfm : StrictMonoOn f s) (hgm : StrictMonoOn g s) :
    (∫ x, f x ∂μ) * (∫ x, g x ∂μ) < ∫ x, f x * g x ∂μ := by
  apply integral_mul_gt_mul_integral_of_strict_comonotone_ae hf hg hfg
  filter_upwards [hs] with x hx
  filter_upwards [hs, μ.ae_ne x] with y hy hyx
  rcases lt_or_gt_of_ne (Ne.symm hyx) with hxy | hyx
  · exact mul_pos_of_neg_of_neg (sub_neg.mpr (hfm hx hy hxy))
      (sub_neg.mpr (hgm hx hy hxy))
  · exact mul_pos (sub_pos.mpr (hfm hy hx hyx)) (sub_pos.mpr (hgm hy hx hyx))

end WishartVerification
end CanonicalSource38

section CanonicalSource39
/- Source: Wishart/SpectralRegressionStrict.lean -/



/-!
# Strict conditional determinant moments in each active spectral coordinate

The residual Wishart matrix is positive definite almost surely. After fixing
it and every Gaussian row except one, the remaining determinant is the exact
Gaussian rank-one determinant of Lemma 3.2 with positive-definite background.
Its strict moment comparison survives integration over the other variables.
All moment and product-law obligations are proved for the actual independent
source, throughout the real nonsingular Wishart shape range.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace Wishart

def shiftedRowsGram {q m : ℕ} (v : Fin q → EuclideanSpace ℝ (Fin m))
    (lam : Fin q → ℝ) (x : RegressionNoise q m) : Matrix (Fin m) (Fin m) ℝ :=
  (x.2 : Matrix (Fin m) (Fin m) ℝ) + ∑ a : Fin q,
    Matrix.vecMulVec (fun i => x.1 a i + Real.sqrt (lam a) * v a i)
      (fun i => x.1 a i + Real.sqrt (lam a) * v a i)

@[fun_prop] theorem measurable_shiftedRowsGram {q m : ℕ}
    (v : Fin q → EuclideanSpace ℝ (Fin m)) (lam : Fin q → ℝ) :
    Measurable (shiftedRowsGram v lam) := by
  apply Matrix.measurable_iff.mpr
  intro i j
  simp only [shiftedRowsGram, Matrix.add_apply, Matrix.sum_apply, Matrix.vecMulVec_apply]
  have hrow (a : Fin q) (b : Fin m) :
      Measurable (fun x : RegressionNoise q m => x.1 a b) :=
    (PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) b).measurable.comp
      ((measurable_pi_apply a).comp measurable_fst)
  have hW : Measurable (fun x : RegressionNoise q m =>
      (x.2 : Matrix (Fin m) (Fin m) ℝ) i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
      (measurable_subtype_coe.comp measurable_snd))
  apply hW.add
  apply Finset.measurable_sum
  intro a ha
  exact ((hrow a i).add_const _).mul ((hrow a j).add_const _)

theorem shiftedRowsGram_posDef {q m : ℕ}
    (v : Fin q → EuclideanSpace ℝ (Fin m)) (lam : Fin q → ℝ)
    (x : RegressionNoise q m) (hW : (x.2 : Matrix (Fin m) (Fin m) ℝ).PosDef) :
    (shiftedRowsGram v lam x).PosDef := by
  apply hW.add_posSemidef
  apply Matrix.posSemidef_sum
  intro a _
  simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star
    (fun i => x.1 a i + Real.sqrt (lam a) * v a i)

section GeneralResidual

variable {q m : ℕ} {ν : Measure (SymmetricMatrix m)} [IsProbabilityMeasure ν]
variable (C : Matrix (Fin m) (Fin m) ℝ)

def gaussianResidualMeasure (q : ℕ) (C : Matrix (Fin m) (Fin m) ℝ)
    (ν : Measure (SymmetricMatrix m)) : Measure (RegressionNoise q m) :=
  (Measure.pi (fun _ : Fin q => multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) C)).prod ν

instance isProbabilityMeasure_gaussianResidualMeasure :
    IsProbabilityMeasure (gaussianResidualMeasure q C ν) := by
  unfold gaussianResidualMeasure
  infer_instance

theorem allFiniteMoments_shiftedRowsGram_entry
    (hν : ∀ i j : Fin m, WishartVerification.HasAllFiniteMoments
      (fun W : SymmetricMatrix m => (W : Matrix (Fin m) (Fin m) ℝ) i j) ν)
    (v : Fin q → EuclideanSpace ℝ (Fin m)) (lam : Fin q → ℝ) (i j : Fin m) :
    WishartVerification.HasAllFiniteMoments (fun x => shiftedRowsGram v lam x i j)
      (gaussianResidualMeasure q C ν) := by
  have hz (a : Fin q) (i : Fin m) :
      WishartVerification.HasAllFiniteMoments
        (fun x : RegressionNoise q m => x.1 a i) (gaussianResidualMeasure q C ν) := by
    exact (WishartVerification.allFiniteMoments_gaussian_coordinate 0 C i).comp_measurePreserving
      ((measurePreserving_eval (fun _ : Fin q =>
        multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) C) a).comp
          measurePreserving_fst)
  have hW := (hν i j).comp_measurePreserving
    (measurePreserving_snd : MeasurePreserving Prod.snd
      (gaussianResidualMeasure q C ν) ν)
  have hy (a : Fin q) (i : Fin m) :
      WishartVerification.HasAllFiniteMoments
        (fun x : RegressionNoise q m => x.1 a i + Real.sqrt (lam a) * v a i)
          (gaussianResidualMeasure q C ν) :=
    (hz a i).add (WishartVerification.HasAllFiniteMoments.const _)
  simpa only [shiftedRowsGram, Matrix.add_apply, Matrix.sum_apply, Matrix.vecMulVec_apply,
    Function.comp_apply, gaussianResidualMeasure] using
    hW.add (WishartVerification.HasAllFiniteMoments.finset_sum Finset.univ
      (fun a x => (x.1 a i + Real.sqrt (lam a) * v a i) *
        (x.1 a j + Real.sqrt (lam a) * v a j))
      (fun a _ => (hy a i).mul (hy a j)))

theorem integrable_shiftedRowsGram_det_rpow
    (hν : ∀ i j : Fin m, WishartVerification.HasAllFiniteMoments
      (fun W : SymmetricMatrix m => (W : Matrix (Fin m) (Fin m) ℝ) i j) ν)
    (v : Fin q → EuclideanSpace ℝ (Fin m)) (lam : Fin q → ℝ)
    {η : ℝ} (hη : 0 ≤ η) :
    Integrable (fun x => (shiftedRowsGram v lam x).det ^ η)
      (gaussianResidualMeasure q C ν) :=
  ((WishartVerification.HasAllFiniteMoments.det _
    (allFiniteMoments_shiftedRowsGram_entry C hν v lam)).rpow hη).integrable

end GeneralResidual

def splitRegressionRow {q m : ℕ} (a : Fin (q + 1))
    (x : RegressionNoise (q + 1) m) : RegressionNoise q m × EuclideanSpace ℝ (Fin m) :=
  ((fun j => x.1 (a.succAbove j), x.2), x.1 a)

theorem measurePreserving_splitRegressionRow {q m : ℕ}
    (C : Matrix (Fin m) (Fin m) ℝ) (ν : Measure (SymmetricMatrix m)) [SFinite ν]
    (a : Fin (q + 1)) :
    MeasurePreserving (splitRegressionRow (m := m) a)
      (gaussianResidualMeasure (q + 1) C ν)
      ((gaussianResidualMeasure q C ν).prod
        (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) C)) := by
  let γ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) C
  have hpi := measurePreserving_piFinSuccAbove (fun _ : Fin (q + 1) => γ) a
  have hprod := hpi.prod (MeasurePreserving.id ν)
  have hassoc := measurePreserving_prodAssoc γ (Measure.pi (fun _ : Fin q => γ)) ν
  have hswap : MeasurePreserving Prod.swap
      (γ.prod ((Measure.pi (fun _ : Fin q => γ)).prod ν))
      (((Measure.pi (fun _ : Fin q => γ)).prod ν).prod γ) := Measure.measurePreserving_swap
  exact hswap.comp (hassoc.comp hprod)

theorem shiftedRowsGram_split {q m : ℕ}
    (v : Fin (q + 1) → EuclideanSpace ℝ (Fin m)) (lam : Fin (q + 1) → ℝ)
    (a : Fin (q + 1)) (t : ℝ) (x : RegressionNoise (q + 1) m) :
    shiftedRowsGram v (Function.update lam a t) x =
      shiftedRowsGram (v ∘ a.succAbove) (lam ∘ a.succAbove) (splitRegressionRow a x).1 +
        Matrix.vecMulVec (x.1 a + Real.sqrt t • v a).ofLp
          (x.1 a + Real.sqrt t • v a).ofLp := by
  unfold shiftedRowsGram
  rw [Fin.sum_univ_succAbove _ a]
  simp only [Function.update_self, Function.update_of_ne (Fin.succAbove_ne _ _),
    splitRegressionRow, Function.comp_apply, WithLp.ofLp_add, WithLp.ofLp_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ext i j
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.vecMulVec_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  abel

/-- Strictness survives mixing a positive-definite random background. The
integrability assumptions on the background are actual all-order entry moments;
the Wishart corollary below proves them from the verified Wishart law. -/
theorem strictMono_shiftedRowsGram_moment
    {q m : ℕ} {ν : Measure (SymmetricMatrix m)} [IsProbabilityMeasure ν]
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosSemidef)
    (hν : ∀ i j : Fin m, WishartVerification.HasAllFiniteMoments
      (fun W : SymmetricMatrix m => (W : Matrix (Fin m) (Fin m) ℝ) i j) ν)
    (hνpd : ∀ᵐ W : SymmetricMatrix m ∂ν, (W : Matrix (Fin m) (Fin m) ℝ).PosDef)
    (v : Fin q → EuclideanSpace ℝ (Fin m)) (lam : Fin q → ℝ)
    (a : Fin q) (hv : v a ≠ 0) {η : ℝ} (hη : 0 < η) :
    StrictMonoOn (fun t : ℝ => ∫ x,
      (shiftedRowsGram v (Function.update lam a t) x).det ^ η
        ∂gaussianResidualMeasure q C ν) (Set.Ici 0) := by
  cases q with
  | zero => exact Fin.elim0 a
  | succ q =>
    let γ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) C
    let μ := gaussianResidualMeasure q C ν
    let B : RegressionNoise q m → Matrix (Fin m) (Fin m) ℝ :=
      shiftedRowsGram (v ∘ a.succAbove) (lam ∘ a.succAbove)
    let F (t : ℝ) (y : RegressionNoise q m × EuclideanSpace ℝ (Fin m)) : ℝ :=
      WishartVerification.rankOneDeterminant (B y.1) (v a) t y.2 ^ η
    have hsplit := measurePreserving_splitRegressionRow C ν a
    have hFmeas (t : ℝ) : Measurable (F t) := by
      dsimp [F, B, WishartVerification.rankOneDeterminant]
      fun_prop
    have hFcomp (t : ℝ) : F t ∘ splitRegressionRow a =
        fun x => (shiftedRowsGram v (Function.update lam a t) x).det ^ η := by
      funext x
      dsimp only [Function.comp_apply, F, WishartVerification.rankOneDeterminant, B]
      rw [shiftedRowsGram_split]
      rfl
    have hFi (t : ℝ) : Integrable (F t) (μ.prod γ) := by
      rw [← hsplit.map_eq]
      apply (integrable_map_measure (hFmeas t).aestronglyMeasurable hsplit.measurable.aemeasurable).mpr
      rw [hFcomp]
      exact integrable_shiftedRowsGram_det_rpow C hν v (Function.update lam a t) hη.le
    have heq (t : ℝ) :
        (∫ x, (shiftedRowsGram v (Function.update lam a t) x).det ^ η
          ∂gaussianResidualMeasure (q + 1) C ν) =
        ∫ y, ∫ z, F t (y, z) ∂γ ∂μ := by
      rw [← integral_prod _ (hFi t), ← hsplit.map_eq,
        integral_map hsplit.measurable.aemeasurable (hFmeas t).aestronglyMeasurable]
      exact congrArg (fun f => ∫ x, f x ∂gaussianResidualMeasure (q + 1) C ν) (hFcomp t).symm
    have hBpd : ∀ᵐ y ∂μ, (B y).PosDef := by
      have hW : ∀ᵐ y ∂μ, (y.2 : Matrix (Fin m) (Fin m) ℝ).PosDef :=
        Measure.quasiMeasurePreserving_snd.ae hνpd
      filter_upwards [hW] with y hy
      exact shiftedRowsGram_posDef _ _ y hy
    intro s hs t ht hst
    dsimp only
    rw [heq s, heq t]
    have hstrict : ∀ᵐ y ∂μ, (∫ z, F s (y, z) ∂γ) < ∫ z, F t (y, z) ∂γ := by
      filter_upwards [hBpd] with y hy
      exact WishartVerification.integral_gaussian_rankOneDeterminant_rpow_strictMono
        hy hC hv hη hs ht hst
    have hp := WishartVerification.integral_pos_of_pos_ae
      ((hFi t).integral_prod_left.sub (hFi s).integral_prod_left)
      (hstrict.mono fun y hy => sub_pos.mpr hy)
    change 0 < ∫ y, (∫ z, F t (y, z) ∂γ) - (∫ z, F s (y, z) ∂γ) ∂μ at hp
    rw [integral_sub (hFi t).integral_prod_left (hFi s).integral_prod_left] at hp
    exact sub_pos.mp hp

/-- Every active spectral row gives a strictly increasing positive determinant
moment for the actual regression source, with every real n>q+m−1 admitted. -/
theorem strictMono_regressionRowMoment {n : ℝ} {q m : ℕ}
    (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (v : Fin q → EuclideanSpace ℝ (Fin m)) (lam : Fin q → ℝ)
    (a : Fin q) (hv : v a ≠ 0) {η : ℝ} (hη : 0 < η) :
    StrictMonoOn (fun t : ℝ => ∫ x,
      (shiftedRowsGram v (Function.update lam a t) x).det ^ η
        ∂regressionNoiseMeasure n q m C) (Set.Ici 0) := by
  have hdegree : (m : ℝ) - 1 < n - q := by
    push_cast at hn
    linarith
  letI := isProbabilityMeasure_nonsingularWishartMeasure hC hdegree
  simpa only [regressionNoiseMeasure, gaussianResidualMeasure] using
    strictMono_shiftedRowsGram_moment hC.posSemidef
    (fun i j => WishartVerification.allFiniteMoments_wishart_entry
      (α := n - q) (Sigma := C) i j)
    (ae_posDef_nonsingularWishartMeasure (n - q) C) v lam a hv hη

theorem regressionGramWithMean_spectral_eq_shiftedRowsGram {q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) (O : Matrix (Fin q) (Fin q) ℝ)
    (lam : Fin q → ℝ) (x : RegressionNoise q m) :
    ((regressionGramWithMean (spectralRegressionMean K O lam) x : SymmetricMatrix m) :
      Matrix (Fin m) (Fin m) ℝ) =
      shiftedRowsGram (fun a => WithLp.toLp 2 (fun i => (Oᵀ * K) a i)) lam x := by
  ext i j
  simp only [regressionGramWithMean, shiftedRowsGram, gaussianRowMatrix,
    Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
    Matrix.vecMulVec_apply, Matrix.sum_apply, spectralRegressionMean_apply, PiLp.toLp_apply]
  simp only [add_comm]

theorem regressionGramWithMean_eq_shiftedRowsGram {q m : ℕ}
    (M : Matrix (Fin m) (Fin q) ℝ) (x : RegressionNoise q m) :
    ((regressionGramWithMean M x : SymmetricMatrix m) : Matrix (Fin m) (Fin m) ℝ) =
      shiftedRowsGram (fun a => WithLp.toLp 2 (fun i => M i a)) (fun _ => 1) x := by
  ext i j
  simp only [regressionGramWithMean, shiftedRowsGram, gaussianRowMatrix,
    Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
    Matrix.vecMulVec_apply, Matrix.sum_apply, PiLp.toLp_apply, Real.sqrt_one, one_mul]
  simp only [add_comm]

theorem allFiniteMoments_regressionGramWithMean_entry
    {n : ℝ} {q m : ℕ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (M : Matrix (Fin m) (Fin q) ℝ) (i j : Fin m) :
    WishartVerification.HasAllFiniteMoments
      (fun x : RegressionNoise q m =>
        ((regressionGramWithMean M x : SymmetricMatrix m) : Matrix (Fin m) (Fin m) ℝ) i j)
      (regressionNoiseMeasure n q m C) := by
  have hdegree : (m : ℝ) - 1 < n - q := by
    push_cast at hn
    linarith
  letI := isProbabilityMeasure_nonsingularWishartMeasure hC hdegree
  simpa only [regressionGramWithMean_eq_shiftedRowsGram, regressionNoiseMeasure,
    gaussianResidualMeasure] using
    allFiniteMoments_shiftedRowsGram_entry
      (ν := nonsingularWishartMeasure (n - q) C) C
      (fun i j => WishartVerification.allFiniteMoments_wishart_entry
        (α := n - q) (Sigma := C) i j)
      (fun a => WithLp.toLp 2 (fun i => M i a)) (fun _ => 1) i j

/-- The strictness statement in the spectral regression coordinates used by
the equality proof. No orthogonality assumption is needed for this last step;
only the displayed row of OᵀK must be nonzero. -/
theorem strictMono_spectralRegression_determinant_moment
    {n : ℝ} {q m : ℕ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (K : Matrix (Fin q) (Fin m) ℝ) (O : Matrix (Fin q) (Fin q) ℝ)
    (lam : Fin q → ℝ) (a : Fin q) (hrow : (fun i => (Oᵀ * K) a i) ≠ 0)
    {η : ℝ} (hη : 0 < η) :
    StrictMonoOn (fun t : ℝ => ∫ x,
      (((regressionGramWithMean (spectralRegressionMean K O (Function.update lam a t)) x :
        SymmetricMatrix m) : Matrix (Fin m) (Fin m) ℝ).det) ^ η
        ∂regressionNoiseMeasure n q m C) (Set.Ici 0) := by
  have hv : (WithLp.toLp 2 (fun i => (Oᵀ * K) a i) : EuclideanSpace ℝ (Fin m)) ≠ 0 := by
    intro h
    exact hrow (congrArg WithLp.ofLp h)
  simpa only [regressionGramWithMean_spectral_eq_shiftedRowsGram] using
    strictMono_regressionRowMoment hn hC
      (fun a => WithLp.toLp 2 (fun i => (Oᵀ * K) a i)) lam a hv hη

end Wishart
end
end CanonicalSource39

section CanonicalSource40
/- Source: Wishart/RegressionMoments.lean -/



/-!
# Actual selected, remaining, and joint moments in regression coordinates

These identities refer to the genuine real-shape Wishart measure. Their
integrability hypotheses concern the displayed actual observables and are
discharged by the determinant moment theorems in the principal application.
The conditional function is an explicit integral over the proved independent
Gaussian/residual source, not an unspecified conditional expectation.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti TauCeti.Probability
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace Wishart

def regressionTailModel {q m : ℕ} (K : Matrix (Fin q) (Fin m) ℝ)
    (S : SymmetricMatrix q) (x : RegressionNoise q m) : SymmetricMatrix m :=
  regressionGramWithMean (Kᵀ * CFC.sqrt (S : Matrix (Fin q) (Fin q) ℝ)) x

@[fun_prop] theorem measurable_regressionTailModel {q m : ℕ}
    (K : Matrix (Fin q) (Fin m) ℝ) :
    Measurable (Function.uncurry (regressionTailModel K)) := by
  have h := (measurable_principalSymmetricBlock (Fin.natAdd q)).comp
    (measurable_regressionReconstruction K)
  change Measurable (fun x : RegressionData q m =>
    principalSymmetricBlock (Fin.natAdd q) (regressionReconstruction K x)) at h
  change Measurable (fun x : RegressionData q m =>
    regressionGramWithMean (Kᵀ * CFC.sqrt (x.1 : Matrix (Fin q) (Fin q) ℝ)) x.2)
  simpa only [regressionReconstruction_trailing] using h

def regressionConditionalMoment {q m : ℕ} (n : ℝ)
    (C : Matrix (Fin m) (Fin m) ℝ) (K : Matrix (Fin q) (Fin m) ℝ)
    (g : SymmetricMatrix m → ℝ) (S : SymmetricMatrix q) : ℝ :=
  ∫ x, g (regressionTailModel K S x) ∂regressionNoiseMeasure n q m C

@[fun_prop] theorem measurable_regressionConditionalMoment {q m : ℕ} (n : ℝ)
    (C : Matrix (Fin m) (Fin m) ℝ) (K : Matrix (Fin q) (Fin m) ℝ)
    {g : SymmetricMatrix m → ℝ} (hg : Measurable g) :
    Measurable (regressionConditionalMoment n C K g) :=
  (hg.comp (measurable_regressionTailModel K)).stronglyMeasurable.integral_prod_right'.measurable

theorem map_regressionSelectedBlock {q m : ℕ} {n : ℝ}
    (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef) :
    (nonsingularWishartMeasure n (regressionScale K C)).map
      (principalSymmetricBlock (Fin.castAdd m)) =
      nonsingularWishartMeasure n (1 : Matrix (Fin q) (Fin q) ℝ) := by
  letI := isProbabilityMeasure_regressionNoiseMeasure hn hC
  rw [← map_regressionReconstruction hn K hC,
    Measure.map_map (measurable_principalSymmetricBlock (Fin.castAdd m))
      (measurable_regressionReconstruction K)]
  have hae : principalSymmetricBlock (Fin.castAdd m) ∘ regressionReconstruction K =ᵐ[
      regressionDataMeasure n q m C] Prod.fst := by
    filter_upwards [ae_regressionReconstruction_selected n K C] with x hx
    exact Subtype.ext hx
  rw [Measure.map_congr hae]
  change Measure.map Prod.fst
    ((nonsingularWishartMeasure n (1 : Matrix (Fin q) (Fin q) ℝ)).prod
      (regressionNoiseMeasure n q m C)) = _
  rw [Measure.map_fst_prod, measure_univ, one_smul]

theorem integral_regression_selected {q m : ℕ} {n : ℝ}
    (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    {h : SymmetricMatrix q → ℝ} (hh : Measurable h) :
    (∫ X, h (principalSymmetricBlock (Fin.castAdd m) X)
      ∂nonsingularWishartMeasure n (regressionScale K C)) =
      ∫ S, h S ∂nonsingularWishartMeasure n (1 : Matrix (Fin q) (Fin q) ℝ) := by
  have hi := integral_map
    (μ := nonsingularWishartMeasure n (regressionScale K C))
    (φ := principalSymmetricBlock (Fin.castAdd m))
    (measurable_principalSymmetricBlock _).aemeasurable hh.aestronglyMeasurable
  rw [map_regressionSelectedBlock hn K hC] at hi
  exact hi.symm

theorem integrable_regression_joint_source {q m : ℕ} {n : ℝ}
    (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    {h : SymmetricMatrix q → ℝ} {g : SymmetricMatrix m → ℝ}
    (hjoint : Integrable
      (fun X => h (principalSymmetricBlock (Fin.castAdd m) X) *
        g (principalSymmetricBlock (Fin.natAdd q) X))
      (nonsingularWishartMeasure n (regressionScale K C))) :
    Integrable (fun x : RegressionData q m => h x.1 * g (regressionTailModel K x.1 x.2))
      ((nonsingularWishartMeasure n (1 : Matrix (Fin q) (Fin q) ℝ)).prod
        (regressionNoiseMeasure n q m C)) := by
  have hsource := (integrable_regressionReconstruction_iff hn K hC
    hjoint.aestronglyMeasurable).mp hjoint
  apply hsource.congr
  filter_upwards [ae_regressionReconstruction_selected n K C] with x hx
  have hselected : principalSymmetricBlock (Fin.castAdd m) (regressionReconstruction K x) =
      x.1 := Subtype.ext hx
  rw [hselected, regressionReconstruction_trailing]
  rfl

/-- Exact joint-moment identity, with the selected factor outside the
independent-source expectation. -/
theorem integral_regression_selected_mul_remaining {q m : ℕ} {n : ℝ}
    (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    {h : SymmetricMatrix q → ℝ} {g : SymmetricMatrix m → ℝ}
    (hjoint : Integrable
      (fun X => h (principalSymmetricBlock (Fin.castAdd m) X) *
        g (principalSymmetricBlock (Fin.natAdd q) X))
      (nonsingularWishartMeasure n (regressionScale K C))) :
    (∫ X, h (principalSymmetricBlock (Fin.castAdd m) X) *
        g (principalSymmetricBlock (Fin.natAdd q) X)
      ∂nonsingularWishartMeasure n (regressionScale K C)) =
      ∫ S, h S * regressionConditionalMoment n C K g S
        ∂nonsingularWishartMeasure n (1 : Matrix (Fin q) (Fin q) ℝ) := by
  rw [integral_regressionReconstruction hn K hC hjoint.aestronglyMeasurable]
  have hae :
      (fun x : RegressionData q m =>
        h (principalSymmetricBlock (Fin.castAdd m) (regressionReconstruction K x)) *
          g (principalSymmetricBlock (Fin.natAdd q) (regressionReconstruction K x))) =ᵐ[
            regressionDataMeasure n q m C]
        (fun x => h x.1 * g (regressionTailModel K x.1 x.2)) := by
    filter_upwards [ae_regressionReconstruction_selected n K C] with x hx
    have hselected : principalSymmetricBlock (Fin.castAdd m) (regressionReconstruction K x) =
        x.1 := Subtype.ext hx
    rw [hselected, regressionReconstruction_trailing]
    rfl
  rw [integral_congr_ae hae]
  change (∫ x : RegressionData q m, h x.1 * g (regressionTailModel K x.1 x.2)
    ∂((nonsingularWishartMeasure n (1 : Matrix (Fin q) (Fin q) ℝ)).prod
      (regressionNoiseMeasure n q m C))) = _
  rw [integral_prod _ (integrable_regression_joint_source hn K hC hjoint)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun S => integral_const_mul (h S) _

theorem integral_regression_remaining {q m : ℕ} {n : ℝ}
    (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    {g : SymmetricMatrix m → ℝ}
    (hg : Integrable (fun X => g (principalSymmetricBlock (Fin.natAdd q) X))
      (nonsingularWishartMeasure n (regressionScale K C))) :
    (∫ X, g (principalSymmetricBlock (Fin.natAdd q) X)
      ∂nonsingularWishartMeasure n (regressionScale K C)) =
      ∫ S, regressionConditionalMoment n C K g S
        ∂nonsingularWishartMeasure n (1 : Matrix (Fin q) (Fin q) ℝ) := by
  simpa only [one_mul] using
    integral_regression_selected_mul_remaining hn K hC
      (h := fun _ => 1) (g := g) (by simpa only [one_mul] using hg)

theorem integrable_regressionConditionalMoment {q m : ℕ} {n : ℝ}
    (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    {g : SymmetricMatrix m → ℝ}
    (hg : Integrable (fun X => g (principalSymmetricBlock (Fin.natAdd q) X))
      (nonsingularWishartMeasure n (regressionScale K C))) :
    Integrable (regressionConditionalMoment n C K g)
      (nonsingularWishartMeasure n (1 : Matrix (Fin q) (Fin q) ℝ)) := by
  have hsource := integrable_regression_joint_source hn K hC
    (h := fun _ => 1) (g := g) (by simpa only [one_mul] using hg)
  unfold regressionConditionalMoment
  simpa only [one_mul] using hsource.integral_prod_left

theorem integrable_regression_selected_mul_conditional {q m : ℕ} {n : ℝ}
    (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    (K : Matrix (Fin q) (Fin m) ℝ)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    {h : SymmetricMatrix q → ℝ} {g : SymmetricMatrix m → ℝ}
    (hjoint : Integrable
      (fun X => h (principalSymmetricBlock (Fin.castAdd m) X) *
        g (principalSymmetricBlock (Fin.natAdd q) X))
      (nonsingularWishartMeasure n (regressionScale K C))) :
    Integrable (fun S => h S * regressionConditionalMoment n C K g S)
      (nonsingularWishartMeasure n (1 : Matrix (Fin q) (Fin q) ℝ)) := by
  apply (integrable_regression_joint_source hn K hC hjoint).integral_prod_left.congr
  exact Filter.Eventually.of_forall fun S => integral_const_mul (h S) _

def spectralConditionalMoment {q m : ℕ} (n : ℝ)
    (C : Matrix (Fin m) (Fin m) ℝ) (K : Matrix (Fin q) (Fin m) ℝ)
    (g : SymmetricMatrix m → ℝ) (lam : Fin q → ℝ)
    (O : Matrix (Fin q) (Fin q) ℝ) : ℝ :=
  ∫ x, g (regressionGramWithMean (spectralRegressionMean K O lam) x)
    ∂regressionNoiseMeasure n q m C

set_option maxHeartbeats 1200000 in
@[fun_prop] theorem measurable_spectralConditionalMoment {q m : ℕ} (n : ℝ)
    (C : Matrix (Fin m) (Fin m) ℝ) (K : Matrix (Fin q) (Fin m) ℝ)
    {g : SymmetricMatrix m → ℝ} (hg : Measurable g) :
    Measurable (Function.uncurry (spectralConditionalMoment n C K g)) := by
  have hmodel : Measurable (fun y :
      (((Fin q → ℝ) × Matrix (Fin q) (Fin q) ℝ) × RegressionNoise q m) =>
        regressionGramWithMean (spectralRegressionMean K y.1.2 y.1.1) y.2) := by
    exact measurable_regressionGramWithMean_uncurry.comp
      (((measurable_spectralRegressionMean K).comp measurable_fst).prodMk measurable_snd)
  exact (hg.comp hmodel).stronglyMeasurable.integral_prod_right'.measurable

/-- The conditional moment is the actual Gaussian-row spectral-source
integral for every displayed eigendecomposition, without any extra law premise. -/
theorem regressionConditionalMoment_eq_spectral {q m : ℕ} (n : ℝ)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosSemidef)
    (K : Matrix (Fin q) (Fin m) ℝ) (O : Matrix (Fin q) (Fin q) ℝ)
    (hO : O * Oᵀ = 1) (lam : Fin q → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (S : SymmetricMatrix q)
    (hS : (S : Matrix (Fin q) (Fin q) ℝ) = O * Matrix.diagonal lam * Oᵀ)
    {g : SymmetricMatrix m → ℝ} (hg : Measurable g) :
    regressionConditionalMoment n C K g S = spectralConditionalMoment n C K g lam O := by
  have hmap := map_regressionTail_spectral n hC K O hO lam hlam S hS
  simp_rw [regressionReconstruction_trailing] at hmap
  have hi := congrArg (fun μ : Measure (SymmetricMatrix m) => ∫ T, g T ∂μ) hmap
  rw [integral_map (measurable_regressionGramWithMean _).aemeasurable hg.aestronglyMeasurable,
    integral_map (measurable_regressionGramWithMean _).aemeasurable hg.aestronglyMeasurable] at hi
  exact hi

/-- Automatic all-order moments for arbitrary finite compression determinant
products on the independent regression source. Positive semidefiniteness of
the offsets is not needed for this integrability assertion. -/
theorem allFiniteMoments_regression_compression_determinant_product
    {n : ℝ} {q m : ℕ} (hn : ((q + m : ℕ) : ℝ) - 1 < n)
    {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosDef)
    (mean : Matrix (Fin m) (Fin q) ℝ)
    {ι : Type*} (J : Finset ι) (k : ι → Type*)
    [∀ i, Fintype (k i)] [∀ i, DecidableEq (k i)]
    (B : ∀ i, Matrix (k i) (k i) ℝ) (M : ∀ i, Matrix (Fin m) (k i) ℝ)
    (η : ι → ℝ) (hη : ∀ i ∈ J, 0 ≤ η i) :
    WishartVerification.HasAllFiniteMoments
      (fun x : RegressionNoise q m => ∏ i ∈ J,
        (B i + (M i)ᵀ *
          ((regressionGramWithMean mean x : SymmetricMatrix m) : Matrix (Fin m) (Fin m) ℝ) *
          M i).det ^ η i) (regressionNoiseMeasure n q m C) := by
  letI := isProbabilityMeasure_regressionNoiseMeasure hn hC
  apply WishartVerification.HasAllFiniteMoments.finset_prod J
  intro a ha
  apply WishartVerification.HasAllFiniteMoments.rpow _ (hη a ha)
  apply WishartVerification.HasAllFiniteMoments.det
  intro i j
  apply (WishartVerification.HasAllFiniteMoments.const (B a i j)).add
  exact WishartVerification.HasAllFiniteMoments.matrix_right_mul_entry _ (M a)
    (fun i j => WishartVerification.HasAllFiniteMoments.matrix_left_mul_entry _ (M a)ᵀ
      (allFiniteMoments_regressionGramWithMean_entry hn hC mean) i j) i j

end Wishart
end
end CanonicalSource40

section CanonicalSource41
/- Source: Wishart/HaarReconstruction.lean -/



/-!
# Reconstructing an invariant law from orbit representatives

This measure identity does not require a measurable choice of a group element
taking the representative to each point. Only the representative itself must be
measurable. It is the probabilistic step used to introduce an independent Haar
frame in spectral disintegration.
-/

open MeasureTheory Function
open scoped ENNReal

namespace Wishart

/-- Averaging a measurable orbit representative against an independent invariant
group element reconstructs an invariant measure. The pointwise orbit witness is
not required to be measurable. -/
theorem map_prod_orbit_representative
    {G X Y : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure G) [IsProbabilityMeasure ν] [ν.IsMulRightInvariant]
    (μ : Measure X) [SFinite μ]
    (act : G → X → X) (selector : X → Y) (repr : Y → X)
    (hact : Measurable (uncurry act))
    (hselector : Measurable selector) (hrepr : Measurable repr)
    (hmul : ∀ g h x, act (g * h) x = act g (act h x))
    (hinv : ∀ g, μ.map (act g) = μ)
    (horbit : ∀ x, ∃ g, act g (repr (selector x)) = x) :
    (ν.prod (μ.map selector)).map (fun p => act p.1 (repr p.2)) = μ := by
  have hbuild : Measurable (fun p : G × Y => act p.1 (repr p.2)) :=
    hact.comp (measurable_fst.prodMk (hrepr.comp measurable_snd))
  apply Measure.ext_of_lintegral
  intro f hf
  have hfg : Measurable (fun p : G × X => f (act p.1 p.2)) := hf.comp hact
  have hfr : Measurable (fun p : G × Y => f (act p.1 (repr p.2))) :=
    hf.comp hbuild
  have havg (x : X) :
      (∫⁻ g, f (act g (repr (selector x))) ∂ν) = ∫⁻ g, f (act g x) ∂ν := by
    obtain ⟨h, hx⟩ := horbit x
    have hm : Measurable (fun g => f (act g (repr (selector x)))) :=
      hf.comp (hact.comp (measurable_id.prodMk measurable_const))
    calc
      (∫⁻ g, f (act g (repr (selector x))) ∂ν) =
          ∫⁻ g, f (act (g * h) (repr (selector x))) ∂ν :=
        ((measurePreserving_mul_right ν h).lintegral_comp hm).symm
      _ = ∫⁻ g, f (act g x) ∂ν := by simp only [hmul, hx]
  calc
    (∫⁻ x, f x ∂(ν.prod (μ.map selector)).map (fun p => act p.1 (repr p.2))) =
        ∫⁻ y, ∫⁻ g, f (act g (repr y)) ∂ν ∂μ.map selector := by
      rw [lintegral_map hf hbuild, lintegral_prod_symm _ hfr.aemeasurable]
    _ = ∫⁻ x, ∫⁻ g, f (act g (repr (selector x))) ∂ν ∂μ :=
      lintegral_map hfr.lintegral_prod_left hselector
    _ = ∫⁻ x, ∫⁻ g, f (act g x) ∂ν ∂μ := lintegral_congr havg
    _ = ∫⁻ g, ∫⁻ x, f (act g x) ∂μ ∂ν :=
      (lintegral_lintegral_swap hfg.aemeasurable).symm
    _ = ∫⁻ g, ∫⁻ x, f x ∂μ ∂ν := by
      apply lintegral_congr
      intro g
      have hg : Measurable (act g) :=
        hact.comp (measurable_const.prodMk measurable_id)
      calc
        (∫⁻ x, f (act g x) ∂μ) = ∫⁻ x, f x ∂μ.map (act g) :=
          (lintegral_map hf hg).symm
        _ = ∫⁻ x, f x ∂μ := by rw [hinv g]
    _ = ∫⁻ x, f x ∂μ := by simp

end Wishart
end CanonicalSource41

section CanonicalSource42
/- Source: Wishart/SpectralReconstruction.lean -/



/-!
# An independent Haar frame for an identity-scale Wishart matrix

The spectrum below uses Mathlib's matrix-indexed enumeration. It is a fixed
reindexing of its decreasing enumeration `eigenvalues₀`. No measurable choice of
an eigenbasis is used: the spectral theorem supplies only pointwise witnesses,
and Haar invariance removes those witnesses before integration.

This file establishes the frame part of spectral disintegration. It does not
assert the Vandermonde density of the spectral marginal.
-/

open MeasureTheory Matrix Function
open scoped ENNReal

namespace Wishart.Spectral

abbrev Sym (p : ℕ) := selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)
abbrev Orth (p : ℕ) := Matrix.orthogonalGroup (Fin p) ℝ

noncomputable def coordinateSpectrum {p : ℕ} (S : Sym p) : Fin p → ℝ :=
  (selfAdjoint.isHermitian_coe S).eigenvalues

noncomputable def diagonalSym {p : ℕ} (lam : Fin p → ℝ) : Sym p :=
  ⟨Matrix.diagonal lam, (Matrix.isHermitian_diagonal lam)⟩

noncomputable def conjugate {p : ℕ} (O : Orth p) : Sym p → Sym p :=
  Matrix.symmetricCongruenceLinearMap (O : Matrix (Fin p) (Fin p) ℝ)

theorem continuous_diagonalSym (p : ℕ) : Continuous (@diagonalSym p) := by
  exact (continuous_id.matrix_diagonal).subtype_mk _

theorem continuous_conjugate (p : ℕ) : Continuous (uncurry (@conjugate p)) := by
  apply Continuous.subtype_mk
  have hc : Continuous (fun x : Orth p × Sym p =>
      (x.1 : Matrix (Fin p) (Fin p) ℝ) * (x.2 : Matrix (Fin p) (Fin p) ℝ) *
        (x.1 : Matrix (Fin p) (Fin p) ℝ)ᵀ) := by fun_prop
  exact hc.congr fun x => (Matrix.coe_symmetricCongruenceLinearMap_apply _ _).symm

theorem conjugate_mul {p : ℕ} (O P : Orth p) (S : Sym p) :
    conjugate (O * P) S = conjugate O (conjugate P S) := by
  simp only [conjugate, Submonoid.coe_mul, Matrix.symmetricCongruenceLinearMap_mul,
    LinearMap.comp_apply]

/-- Each matrix-indexed eigenvalue is continuous in the symmetric matrix. -/
theorem continuous_coordinateSpectrum (p : ℕ) : Continuous (@coordinateSpectrum p) := by
  letI : NormedAddCommGroup (Matrix (Fin p) (Fin p) ℝ) := Matrix.normedAddCommGroup
  let H := {A : Matrix (Fin p) (Fin p) ℝ // A.IsHermitian}
  have hLam (i : Fin p) : LipschitzWith (p : NNReal) (fun A : H => A.2.eigenvalues i) := by
    apply LipschitzWith.of_dist_le_mul
    intro A B
    have hb := A.2.abs_eigenvalues₀_sub_le_of_entry_le B.2
      (ε := ‖A.1 - B.1‖)
      (fun j k => by
        simpa only [Matrix.sub_apply] using
          (Matrix.norm_entry_le_entrywise_sup_norm (A.1 - B.1) (i := j) (j := k)))
      ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i)
    have hd : dist A B = ‖A.1 - B.1‖ :=
      (Subtype.dist_eq A B).trans (dist_eq_norm _ _)
    simpa only [Real.dist_eq, Real.norm_eq_abs, hd,
      Matrix.IsHermitian.eigenvalues, Fintype.card_fin, NNReal.coe_natCast] using hb
  have hH : Continuous (fun S : Sym p => (⟨S.1, selfAdjoint.isHermitian_coe S⟩ : H)) :=
    continuous_subtype_val.subtype_mk _
  exact continuous_pi fun i => (hLam i).continuous.comp hH

/-- The spectral theorem is used pointwise; no measurable eigenframe is asserted. -/
theorem exists_conjugate_diagonal_spectrum {p : ℕ} (S : Sym p) :
    ∃ O : Orth p, conjugate O (diagonalSym (coordinateSpectrum S)) = S := by
  let hS := selfAdjoint.isHermitian_coe S
  refine ⟨hS.eigenvectorUnitary, Subtype.ext ?_⟩
  have hs := hS.spectral_theorem
  simpa only [conjugate, Matrix.coe_symmetricCongruenceLinearMap_apply, diagonalSym,
    coordinateSpectrum, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id,
    Function.id_comp] using hs.symm

/-- Orthogonal congruence preserves the identity-scale nonsingular Wishart law. -/
theorem map_conjugate_identity_wishart {p : ℕ} (α : ℝ) (O : Orth p) :
    (TauCeti.Probability.nonsingularWishartMeasure α (1 : Matrix (Fin p) (Fin p) ℝ)).map
        (conjugate O) =
      TauCeti.Probability.nonsingularWishartMeasure α (1 : Matrix (Fin p) (Fin p) ℝ) := by
  have hO : (O : Matrix (Fin p) (Fin p) ℝ).det ≠ 0 :=
    (Matrix.UnitaryGroup.det_isUnit O).ne_zero
  have hOO : (O : Matrix (Fin p) (Fin p) ℝ) *
      (O : Matrix (Fin p) (Fin p) ℝ)ᵀ = 1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using Unitary.coe_mul_star_self O
  simpa only [conjugate, Matrix.mul_one, hOO] using
    TauCeti.Probability.map_symmetricCongruenceLinearMap_nonsingularWishartMeasure_of_det_ne_zero
      α (1 : Matrix (Fin p) (Fin p) ℝ) hO

/-- Sampling the exact spectral marginal and an independent Haar orthogonal frame
reconstructs the real-shape identity-scale Wishart law. -/
theorem haar_spectral_reconstruction {p : ℕ} {α : ℝ} (hα : (p : ℝ) - 1 < α) :
    ((TauCeti.haarProb (Orth p)).prod
      ((TauCeti.Probability.nonsingularWishartMeasure α
        (1 : Matrix (Fin p) (Fin p) ℝ)).map coordinateSpectrum)).map
      (fun x => conjugate x.1 (diagonalSym x.2)) =
      TauCeti.Probability.nonsingularWishartMeasure α
        (1 : Matrix (Fin p) (Fin p) ℝ) := by
  letI := TauCeti.Probability.isProbabilityMeasure_nonsingularWishartMeasure
    (Matrix.PosDef.one : (1 : Matrix (Fin p) (Fin p) ℝ).PosDef) hα
  exact Wishart.map_prod_orbit_representative (TauCeti.haarProb (Orth p))
    (TauCeti.Probability.nonsingularWishartMeasure α (1 : Matrix (Fin p) (Fin p) ℝ))
    conjugate coordinateSpectrum diagonalSym (continuous_conjugate p).measurable
    (continuous_coordinateSpectrum p).measurable (continuous_diagonalSym p).measurable
    conjugate_mul (map_conjugate_identity_wishart α) exists_conjugate_diagonal_spectrum

end Wishart.Spectral
end CanonicalSource42

section CanonicalSource43
/- Source: Wishart/CayleyChart.lean -/



/-!
# The real skew-symmetric Cayley chart

The Cayley transform is defined on every real skew-symmetric matrix. Its inverse
is available on its image, and no exponential injectivity assertion is used.
These algebraic identities underlie a local spectral change of variables.
-/

open Matrix

namespace Wishart.Spectral

abbrev Skew (p : ℕ) := skewAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)

theorem transpose_skew {p : ℕ} (S : Skew p) :
    (S : Matrix (Fin p) (Fin p) ℝ)ᵀ = -(S : Matrix (Fin p) (Fin p) ℝ) := by
  have hs : star (S : Matrix (Fin p) (Fin p) ℝ) =
      -(S : Matrix (Fin p) (Fin p) ℝ) := S.property
  simpa only [Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] using hs

/-- A real skew-symmetric matrix has no eigenvalue `-1`. -/
theorem det_one_add_skew_ne_zero {p : ℕ} {S : Matrix (Fin p) (Fin p) ℝ}
    (hS : Sᵀ = -S) : (1 + S).det ≠ 0 := by
  have hgram : (Sᵀ * S).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self S
  have hp : (1 + Sᵀ * S).PosDef := Matrix.PosDef.one.add_posSemidef hgram
  have heq : (1 + S)ᵀ * (1 + S) = 1 + Sᵀ * S := by
    rw [Matrix.transpose_add, Matrix.transpose_one, hS]
    noncomm_ring
  intro hz
  have hpos := hp.det_pos
  rw [← heq, Matrix.det_mul, Matrix.det_transpose, hz, zero_mul] at hpos
  exact (lt_irrefl (0 : ℝ)) hpos

theorem det_one_sub_skew_ne_zero {p : ℕ} {S : Matrix (Fin p) (Fin p) ℝ}
    (hS : Sᵀ = -S) : (1 - S).det ≠ 0 := by
  have hneg : (-S)ᵀ = -(-S) := by rw [Matrix.transpose_neg, hS]
  simpa only [sub_eq_add_neg] using det_one_add_skew_ne_zero hneg

noncomputable def cayleyMatrix {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ) :
    Matrix (Fin p) (Fin p) ℝ := (1 - S) * (1 + S)⁻¹

/-- The real Cayley transform is orthogonal. -/
theorem cayleyMatrix_mem_orthogonal {p : ℕ} {S : Matrix (Fin p) (Fin p) ℝ}
    (hS : Sᵀ = -S) : cayleyMatrix S ∈ Orth p := by
  have hplus : IsUnit (1 + S).det := isUnit_iff_ne_zero.mpr (det_one_add_skew_ne_zero hS)
  have hminus : IsUnit (1 - S).det := isUnit_iff_ne_zero.mpr (det_one_sub_skew_ne_zero hS)
  have hcomm : (1 + S) * (1 - S) = (1 - S) * (1 + S) := by noncomm_ring
  apply (Matrix.mem_orthogonalGroup_iff' (Fin p) ℝ).mpr
  unfold cayleyMatrix
  rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv,
    Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_one, hS]
  simp only [sub_neg_eq_add, ← sub_eq_add_neg]
  calc
    (1 - S)⁻¹ * (1 + S) * ((1 - S) * (1 + S)⁻¹) =
        (1 - S)⁻¹ * ((1 + S) * (1 - S)) * (1 + S)⁻¹ := by
          simp only [Matrix.mul_assoc]
    _ = (1 - S)⁻¹ * ((1 - S) * (1 + S)) * (1 + S)⁻¹ := by rw [hcomm]
    _ = 1 := by
      rw [Matrix.nonsing_inv_mul_cancel_left _ _ hminus,
        Matrix.mul_nonsing_inv _ hplus]

noncomputable def cayley {p : ℕ} (S : Skew p) : Orth p :=
  ⟨cayleyMatrix S, cayleyMatrix_mem_orthogonal (transpose_skew S)⟩

@[simp] theorem cayley_zero (p : ℕ) : cayley (0 : Skew p) = 1 := by
  apply Subtype.ext
  simp [cayley, cayleyMatrix]

/-- Multiplying the Cayley transform by its denominator recovers the numerator. -/
theorem cayleyMatrix_mul_one_add {p : ℕ} {S : Matrix (Fin p) (Fin p) ℝ}
    (hS : Sᵀ = -S) : cayleyMatrix S * (1 + S) = 1 - S := by
  exact Matrix.nonsing_inv_mul_cancel_right _ _
    (isUnit_iff_ne_zero.mpr (det_one_add_skew_ne_zero hS))

/-- The denominator of the inverse Cayley map is invertible on the chart. -/
theorem one_add_cayleyMatrix {p : ℕ} {S : Matrix (Fin p) (Fin p) ℝ}
    (hS : Sᵀ = -S) : 1 + cayleyMatrix S = (2 : ℝ) • (1 + S)⁻¹ := by
  have hplus : IsUnit (1 + S).det := isUnit_iff_ne_zero.mpr (det_one_add_skew_ne_zero hS)
  calc
    1 + cayleyMatrix S = (1 + S) * (1 + S)⁻¹ + (1 - S) * (1 + S)⁻¹ := by
      rw [Matrix.mul_nonsing_inv _ hplus]
      rfl
    _ = ((1 + S) + (1 - S)) * (1 + S)⁻¹ := by noncomm_ring
    _ = (2 : ℝ) • (1 + S)⁻¹ := by
      have heq : (1 + S) + (1 - S) = (2 : ℝ) • (1 : Matrix (Fin p) (Fin p) ℝ) := by
        simp only [two_smul]
        abel
      rw [heq, Matrix.smul_mul, Matrix.one_mul]

/-- The Cayley map is injective on all real skew-symmetric matrices. -/
theorem cayley_injective (p : ℕ) : Function.Injective (@cayley p) := by
  intro S T hST
  have hmatrix : cayleyMatrix (S : Matrix (Fin p) (Fin p) ℝ) = cayleyMatrix T :=
    congrArg Subtype.val hST
  have hinv : (1 + (S : Matrix (Fin p) (Fin p) ℝ))⁻¹ =
      (1 + (T : Matrix (Fin p) (Fin p) ℝ))⁻¹ := by
    apply smul_right_injective _ (by norm_num : (2 : ℝ) ≠ 0)
    change (2 : ℝ) • (1 + (S : Matrix (Fin p) (Fin p) ℝ))⁻¹ =
      (2 : ℝ) • (1 + (T : Matrix (Fin p) (Fin p) ℝ))⁻¹
    rw [← one_add_cayleyMatrix (transpose_skew S),
      ← one_add_cayleyMatrix (transpose_skew T), hmatrix]
  have hdouble := congrArg (fun A : Matrix (Fin p) (Fin p) ℝ => A⁻¹) hinv
  rw [Matrix.nonsing_inv_nonsing_inv _
      (isUnit_iff_ne_zero.mpr (det_one_add_skew_ne_zero (transpose_skew S))),
    Matrix.nonsing_inv_nonsing_inv _
      (isUnit_iff_ne_zero.mpr (det_one_add_skew_ne_zero (transpose_skew T)))] at hdouble
  exact Subtype.ext (add_left_cancel hdouble)

theorem continuous_cayleyMatrix_skew (p : ℕ) :
    Continuous (fun S : Skew p => cayleyMatrix (S : Matrix (Fin p) (Fin p) ℝ)) := by
  apply continuous_iff_continuousAt.mpr
  intro S
  have hden : Continuous (fun T : Skew p => 1 + (T : Matrix (Fin p) (Fin p) ℝ)) := by
    fun_prop
  have hinv : ContinuousAt Inv.inv (1 + (S : Matrix (Fin p) (Fin p) ℝ)) := by
    apply continuousAt_matrix_inv
    simpa only [Ring.inverse_eq_inv'] using
      (continuousAt_inv₀ (det_one_add_skew_ne_zero (transpose_skew S)))
  exact (continuous_const.sub continuous_subtype_val).continuousAt.mul
    (hinv.comp (f := fun T : Skew p => 1 + (T : Matrix (Fin p) (Fin p) ℝ))
      hden.continuousAt)

theorem continuous_cayley (p : ℕ) : Continuous (@cayley p) :=
  (continuous_cayleyMatrix_skew p).subtype_mk _

/-- The local window used to remove the sign ambiguity of an eigenframe. -/
def cayleyWindow (p : ℕ) : Set (Skew p) :=
  {S | ∀ i : Fin p, 0 < (cayley S : Matrix (Fin p) (Fin p) ℝ) i i}

theorem isOpen_cayleyWindow (p : ℕ) : IsOpen (cayleyWindow p) := by
  simp only [cayleyWindow, Set.setOf_forall]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_lt continuous_const
    ((continuous_cayleyMatrix_skew p).matrix_elem i i)

theorem zero_mem_cayleyWindow (p : ℕ) : (0 : Skew p) ∈ cayleyWindow p := by
  intro i
  simp [cayley_zero]

end Wishart.Spectral
end CanonicalSource43

section CanonicalSource44
/- Source: Wishart/SpectralInjectivity.lean -/



/-!
# Removing eigenframe signs in the local spectral chart

For a simple fixed spectrum, two orthogonal frames producing the same symmetric
matrix differ by independent column signs. Requiring positive diagonal entries
on both frames forces all those signs to be positive. This is the injectivity
step for the small Cayley chart.
-/

open Matrix

namespace Wishart.Spectral

theorem orth_mul_transpose {p : ℕ} (O : Orth p) :
    (O : Matrix (Fin p) (Fin p) ℝ) * (O : Matrix (Fin p) (Fin p) ℝ)ᵀ = 1 :=
  (Matrix.mem_orthogonalGroup_iff (Fin p) ℝ).mp O.property

theorem orth_transpose_mul {p : ℕ} (O : Orth p) :
    (O : Matrix (Fin p) (Fin p) ℝ)ᵀ * (O : Matrix (Fin p) (Fin p) ℝ) = 1 :=
  (Matrix.mem_orthogonalGroup_iff' (Fin p) ℝ).mp O.property

theorem conjugate_one {p : ℕ} (S : Sym p) : conjugate (1 : Orth p) S = S := by
  simp only [conjugate, Submonoid.coe_one, Matrix.symmetricCongruenceLinearMap_one,
    LinearMap.id_apply]

/-- Commuting with a diagonal matrix with distinct entries forces a matrix to
be diagonal. -/
theorem eq_diagonal_of_commute_diagonal {p : ℕ}
    (d : Fin p → ℝ) (hd : Function.Injective d)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * Matrix.diagonal d = Matrix.diagonal d * A) :
    A = Matrix.diagonal (fun i => A i i) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · have he := congrFun (congrFun hA i) j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at he
    have hdij : d j - d i ≠ 0 := sub_ne_zero.mpr (fun h => hij (hd h.symm))
    have hz : (d j - d i) * A i j = 0 := by nlinarith [he]
    have ha : A i j = 0 := (mul_eq_zero.mp hz).resolve_left hdij
    simp [Matrix.diagonal_apply, hij, ha]

/-- The positive-diagonal frame window has no eigenvector-sign ambiguity. -/
theorem orthogonal_eq_of_conjugate_diagonal_eq_of_pos_diag {p : ℕ}
    (d : Fin p → ℝ) (hd : Function.Injective d) (Q P : Orth p)
    (hQ : ∀ i, 0 < (Q : Matrix (Fin p) (Fin p) ℝ) i i)
    (hP : ∀ i, 0 < (P : Matrix (Fin p) (Fin p) ℝ) i i)
    (hconj : conjugate Q (diagonalSym d) = conjugate P (diagonalSym d)) : Q = P := by
  let E : Orth p := P⁻¹ * Q
  have hQPE : Q = P * E := by simp [E]
  have hfix : conjugate E (diagonalSym d) = diagonalSym d := by
    dsimp [E]
    rw [conjugate_mul, hconj, ← conjugate_mul, inv_mul_cancel, conjugate_one]
  have hfixM : (E : Matrix (Fin p) (Fin p) ℝ) * Matrix.diagonal d *
      (E : Matrix (Fin p) (Fin p) ℝ)ᵀ = Matrix.diagonal d := by
    have h := congrArg Subtype.val hfix
    simpa only [conjugate, Matrix.coe_symmetricCongruenceLinearMap_apply,
      diagonalSym] using h
  have hcomm : (E : Matrix (Fin p) (Fin p) ℝ) * Matrix.diagonal d =
      Matrix.diagonal d * (E : Matrix (Fin p) (Fin p) ℝ) := by
    have h := congrArg (fun A : Matrix (Fin p) (Fin p) ℝ =>
      A * (E : Matrix (Fin p) (Fin p) ℝ)) hfixM
    simpa only [Matrix.mul_assoc, orth_transpose_mul, Matrix.mul_one] using h
  let e : Fin p → ℝ := fun i => (E : Matrix (Fin p) (Fin p) ℝ) i i
  have hdiag : (E : Matrix (Fin p) (Fin p) ℝ) = Matrix.diagonal e :=
    eq_diagonal_of_commute_diagonal d hd E hcomm
  have hsquare (i : Fin p) : e i * e i = 1 := by
    have h := orth_transpose_mul E
    rw [hdiag, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal] at h
    simpa only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq] using
      congrFun (congrFun h i) i
  have hentry (i : Fin p) : (Q : Matrix (Fin p) (Fin p) ℝ) i i =
      (P : Matrix (Fin p) (Fin p) ℝ) i i * e i := by
    have h := congrArg (fun U : Orth p => (U : Matrix (Fin p) (Fin p) ℝ)) hQPE
    simp only [Submonoid.coe_mul, hdiag, Matrix.mul_diagonal] at h
    simpa only [Matrix.mul_diagonal] using congrFun (congrFun h i) i
  have he (i : Fin p) : e i = 1 := by
    have hpos : 0 < e i := by nlinarith [hQ i, hP i, hentry i]
    nlinarith [hsquare i]
  have hE : E = 1 := by
    apply Subtype.ext
    rw [hdiag]
    ext i j
    simp [Matrix.diagonal_apply, Matrix.one_apply, he]
  simpa only [hE, mul_one] using hQPE

theorem cayley_spectral_injective_fixed {p : ℕ}
    (d : Fin p → ℝ) (hd : Function.Injective d) :
    Set.InjOn (fun S : Skew p => conjugate (cayley S) (diagonalSym d))
      (cayleyWindow p) := by
  intro S hS T hT hST
  apply cayley_injective p
  exact orthogonal_eq_of_conjugate_diagonal_eq_of_pos_diag d hd
    (cayley S) (cayley T) hS hT hST

end Wishart.Spectral
end CanonicalSource44

section CanonicalSource45
/- Source: Wishart/AscendingSpectrum.lean -/



/-!
# Ascending eigenvalues and their exact spectral representatives

The permutation below reverses Mathlib's decreasing `eigenvalues₀` enumeration.
It is fixed by the dimension, independent of the sampled matrix. All continuity,
orbit reconstruction and chamber statements therefore use literally ascending
coordinates, as in the manuscript and the association theorem.
-/

open Matrix MeasureTheory
open scoped Classical

namespace Wishart.Spectral

noncomputable def ascendingIndexEquiv (p : ℕ) : Equiv.Perm (Fin p) :=
  Fin.revPerm.trans ((finCongr (Fintype.card_fin p).symm).trans
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin p)))))

noncomputable def ascendingSpectrum {p : ℕ} (S : Sym p) : Fin p → ℝ :=
  coordinateSpectrum S ∘ ascendingIndexEquiv p

theorem ascendingSpectrum_eq_eigenvalues₀ {p : ℕ} (S : Sym p) (i : Fin p) :
    ascendingSpectrum S i = (selfAdjoint.isHermitian_coe S).eigenvalues₀
      (Fin.cast (Fintype.card_fin p).symm (Fin.rev i)) := by
  simp only [ascendingSpectrum, coordinateSpectrum, Matrix.IsHermitian.eigenvalues,
    Function.comp_apply, ascendingIndexEquiv, Equiv.trans_apply,
    Equiv.symm_apply_apply, Fin.revPerm_apply, finCongr_apply]

theorem continuous_ascendingSpectrum (p : ℕ) : Continuous (@ascendingSpectrum p) := by
  apply continuous_pi
  intro i
  exact (continuous_apply (ascendingIndexEquiv p i)).comp (continuous_coordinateSpectrum p)

theorem monotone_ascendingSpectrum {p : ℕ} (S : Sym p) : Monotone (ascendingSpectrum S) := by
  intro i j hij
  rw [ascendingSpectrum_eq_eigenvalues₀, ascendingSpectrum_eq_eigenvalues₀]
  apply (selfAdjoint.isHermitian_coe S).eigenvalues₀_antitone
  exact Fin.rev_anti hij

theorem range_ascendingSpectrum {p : ℕ} (S : Sym p) :
    Set.range (ascendingSpectrum S) = Set.range (coordinateSpectrum S) :=
  (ascendingIndexEquiv p).surjective.range_comp (coordinateSpectrum S)

theorem strictMono_ascendingSpectrum {p : ℕ} (S : Sym p)
    (hS : Function.Injective (coordinateSpectrum S)) : StrictMono (ascendingSpectrum S) :=
  (monotone_ascendingSpectrum S).strictMono_of_injective
    (hS.comp (ascendingIndexEquiv p).injective)

def permutationOrth {p : ℕ} (e : Equiv.Perm (Fin p)) : Orth p :=
  ⟨e.permMatrix ℝ, (Matrix.mem_orthogonalGroup_iff (Fin p) ℝ).mpr (by
    rw [Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul, inv_mul_cancel,
      Matrix.permMatrix_one])⟩

theorem conjugate_permutation_diagonal {p : ℕ}
    (e : Equiv.Perm (Fin p)) (lam : Fin p → ℝ) :
    conjugate (permutationOrth e) (diagonalSym lam) = diagonalSym (lam ∘ e) := by
  apply Subtype.ext
  rw [show (conjugate (permutationOrth e) (diagonalSym lam) :
      Matrix (Fin p) (Fin p) ℝ) = (Matrix.diagonal lam).submatrix e e from
    Matrix.coe_symmetricCongruenceLinearMap_permMatrix_apply e (diagonalSym lam)]
  ext i j
  simp only [Matrix.submatrix_apply, diagonalSym, Matrix.diagonal_apply,
    e.injective.eq_iff, Function.comp_apply]

theorem exists_conjugate_diagonal_ascendingSpectrum {p : ℕ} (S : Sym p) :
    ∃ O : Orth p, conjugate O (diagonalSym (ascendingSpectrum S)) = S := by
  obtain ⟨O, hO⟩ := exists_conjugate_diagonal_spectrum S
  let P := permutationOrth (ascendingIndexEquiv p)
  refine ⟨O * P⁻¹, ?_⟩
  change conjugate (O * P⁻¹)
    (diagonalSym (coordinateSpectrum S ∘ ascendingIndexEquiv p)) = S
  rw [← conjugate_permutation_diagonal, ← conjugate_mul]
  simpa only [P, mul_assoc, inv_mul_cancel, mul_one] using hO

theorem charpoly_conjugate {p : ℕ} (O : Orth p) (S : Sym p) :
    (conjugate O S : Matrix (Fin p) (Fin p) ℝ).charpoly =
      (S : Matrix (Fin p) (Fin p) ℝ).charpoly := by
  rw [show (conjugate O S : Matrix (Fin p) (Fin p) ℝ) =
      (O : Matrix (Fin p) (Fin p) ℝ) * (S : Matrix (Fin p) (Fin p) ℝ) *
        (O : Matrix (Fin p) (Fin p) ℝ)ᵀ from
          Matrix.coe_symmetricCongruenceLinearMap_apply _ _,
    Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, orth_transpose_mul, Matrix.one_mul]

theorem ascendingSpectrum_conjugate {p : ℕ} (O : Orth p) (S : Sym p) :
    ascendingSpectrum (conjugate O S) = ascendingSpectrum S := by
  have hspec : coordinateSpectrum (conjugate O S) = coordinateSpectrum S :=
    ((selfAdjoint.isHermitian_coe (conjugate O S)).eigenvalues_eq_eigenvalues_iff
      (selfAdjoint.isHermitian_coe S)).mpr (charpoly_conjugate O S)
  exact congrArg (fun f : Fin p → ℝ => f ∘ ascendingIndexEquiv p) hspec

theorem spectrum_eq_range_ascendingSpectrum {p : ℕ} (S : Sym p) :
    spectrum ℝ (S : Matrix (Fin p) (Fin p) ℝ) = Set.range (ascendingSpectrum S) := by
  rw [range_ascendingSpectrum]
  simpa only [coordinateSpectrum, RCLike.ofReal_real_eq_id, Set.image_id] using
    (selfAdjoint.isHermitian_coe S).spectrum_eq_image_range

theorem spectrum_conjugate_diagonal {p : ℕ} (O : Orth p) (lam : Fin p → ℝ) :
    spectrum ℝ (conjugate O (diagonalSym lam) : Matrix (Fin p) (Fin p) ℝ) =
      Set.range lam := by
  have h := Unitary.spectrum_star_right_conjugate
    (R := ℝ) (a := Matrix.diagonal lam) (U := O)
  simpa only [conjugate, Matrix.coe_symmetricCongruenceLinearMap_apply, diagonalSym,
    Unitary.coe_star, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, spectrum_diagonal] using h

theorem injective_of_range_eq_injective {p : ℕ} {f g : Fin p → ℝ}
    (hg : Function.Injective g) (hr : Set.range f = Set.range g) :
    Function.Injective f := by
  have him : Finset.univ.image f = Finset.univ.image g := by
    ext t
    simpa only [Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range] using
      (Set.ext_iff.mp hr t)
  have hc : (Finset.univ.image f).card = (Finset.univ : Finset (Fin p)).card := by
    rw [him]
    exact Finset.card_image_of_injective _ hg
  intro i j hij
  exact (Finset.card_image_iff.mp hc) (Finset.mem_univ i) (Finset.mem_univ j) hij

/-- On the strict ascending chamber the spectral selector recovers every input
coordinate, not merely the unordered spectrum or its determinant. -/
theorem ascendingSpectrum_conjugate_diagonal {p : ℕ} (O : Orth p)
    (lam : Fin p → ℝ) (hlam : StrictMono lam) :
    ascendingSpectrum (conjugate O (diagonalSym lam)) = lam := by
  have hr : Set.range (ascendingSpectrum (conjugate O (diagonalSym lam))) =
      Set.range lam := by
    rw [← spectrum_eq_range_ascendingSpectrum, spectrum_conjugate_diagonal]
  exact ((monotone_ascendingSpectrum _).strictMono_of_injective
    (injective_of_range_eq_injective hlam.injective hr)).eq_of_range_eq hlam hr

/-- Independent Haar reconstruction, now with the exact ascending enumeration. -/
theorem haar_ascending_spectral_reconstruction {p : ℕ} {α : ℝ}
    (hα : (p : ℝ) - 1 < α) :
    ((TauCeti.haarProb (Orth p)).prod
      ((TauCeti.Probability.nonsingularWishartMeasure α
        (1 : Matrix (Fin p) (Fin p) ℝ)).map ascendingSpectrum)).map
      (fun x => conjugate x.1 (diagonalSym x.2)) =
      TauCeti.Probability.nonsingularWishartMeasure α
        (1 : Matrix (Fin p) (Fin p) ℝ) := by
  letI := TauCeti.Probability.isProbabilityMeasure_nonsingularWishartMeasure
    (Matrix.PosDef.one : (1 : Matrix (Fin p) (Fin p) ℝ).PosDef) hα
  exact Wishart.map_prod_orbit_representative (TauCeti.haarProb (Orth p))
    (TauCeti.Probability.nonsingularWishartMeasure α (1 : Matrix (Fin p) (Fin p) ℝ))
    conjugate ascendingSpectrum diagonalSym (continuous_conjugate p).measurable
    (continuous_ascendingSpectrum p).measurable (continuous_diagonalSym p).measurable
    conjugate_mul (map_conjugate_identity_wishart α) exists_conjugate_diagonal_ascendingSpectrum

end Wishart.Spectral
end CanonicalSource45

section CanonicalSource46
/- Source: Wishart/CayleyInverse.lean -/



/-!
# The inverse of the real Cayley chart

The Cayley map is an involution whenever its denominator is invertible.
Applied to an orthogonal matrix without eigenvalue `-1`, its value is skew
symmetric. This describes the image of the chart without excluding either
component of the orthogonal group by an almost-everywhere assertion.
-/

open Matrix

namespace Wishart.Spectral

theorem cayleyMatrix_mul_one_add_of_isUnit {p : ℕ}
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : IsUnit (1 + S).det) :
    cayleyMatrix S * (1 + S) = 1 - S := by
  exact Matrix.nonsing_inv_mul_cancel_right _ _ hS

theorem one_add_cayleyMatrix_of_isUnit {p : ℕ}
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : IsUnit (1 + S).det) :
    1 + cayleyMatrix S = (2 : ℝ) • (1 + S)⁻¹ := by
  calc
    1 + cayleyMatrix S = (1 + S) * (1 + S)⁻¹ + (1 - S) * (1 + S)⁻¹ := by
      rw [Matrix.mul_nonsing_inv _ hS]
      rfl
    _ = ((1 + S) + (1 - S)) * (1 + S)⁻¹ := by noncomm_ring
    _ = (2 : ℝ) • (1 + S)⁻¹ := by
      have heq : (1 + S) + (1 - S) = (2 : ℝ) • (1 : Matrix (Fin p) (Fin p) ℝ) := by
        simp only [two_smul]
        abel
      rw [heq, Matrix.smul_mul, Matrix.one_mul]

theorem one_add_cayleyMatrix_mul_half {p : ℕ}
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : IsUnit (1 + S).det) :
    (1 + cayleyMatrix S) * ((1 / 2 : ℝ) • (1 + S)) = 1 := by
  rw [one_add_cayleyMatrix_of_isUnit hS, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.nonsing_inv_mul _ hS, smul_smul]
  norm_num

theorem isUnit_det_one_add_cayleyMatrix {p : ℕ}
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : IsUnit (1 + S).det) :
    IsUnit (1 + cayleyMatrix S).det := by
  exact (Matrix.isUnit_iff_isUnit_det _).mp
    (IsUnit.of_mul_eq_one _ (one_add_cayleyMatrix_mul_half hS))

theorem inv_one_add_cayleyMatrix {p : ℕ}
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : IsUnit (1 + S).det) :
    (1 + cayleyMatrix S)⁻¹ = (1 / 2 : ℝ) • (1 + S) :=
  Matrix.inv_eq_right_inv (one_add_cayleyMatrix_mul_half hS)

/-- Cayley inversion is an exact algebraic identity on its natural domain. -/
theorem cayleyMatrix_cayleyMatrix {p : ℕ}
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : IsUnit (1 + S).det) :
    cayleyMatrix (cayleyMatrix S) = S := by
  change (1 - cayleyMatrix S) * (1 + cayleyMatrix S)⁻¹ = S
  rw [inv_one_add_cayleyMatrix hS, Matrix.mul_smul, Matrix.sub_mul,
    Matrix.one_mul, cayleyMatrix_mul_one_add_of_isUnit hS]
  have heq : (1 + S) - (1 - S) = (2 : ℝ) • S := by
    simp only [two_smul]
    abel
  rw [heq, smul_smul]
  norm_num

/-- The inverse Cayley coordinate of an orthogonal matrix is skew symmetric. -/
theorem transpose_cayleyMatrix_of_orthogonal {p : ℕ} (O : Orth p)
    (hO : IsUnit (1 + (O : Matrix (Fin p) (Fin p) ℝ)).det) :
    (cayleyMatrix (O : Matrix (Fin p) (Fin p) ℝ))ᵀ =
      -cayleyMatrix (O : Matrix (Fin p) (Fin p) ℝ) := by
  have hden : IsUnit (1 + (O : Matrix (Fin p) (Fin p) ℝ)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr hO
  have hdenT : IsUnit (1 + (O : Matrix (Fin p) (Fin p) ℝ))ᵀ := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    simpa only [Matrix.det_transpose] using hO
  apply hdenT.mul_right_injective
  apply hden.mul_left_injective
  change ((1 + (O : Matrix (Fin p) (Fin p) ℝ))ᵀ *
      (cayleyMatrix (O : Matrix (Fin p) (Fin p) ℝ))ᵀ) *
        (1 + (O : Matrix (Fin p) (Fin p) ℝ)) =
    ((1 + (O : Matrix (Fin p) (Fin p) ℝ))ᵀ *
      (-cayleyMatrix (O : Matrix (Fin p) (Fin p) ℝ))) *
        (1 + (O : Matrix (Fin p) (Fin p) ℝ))
  rw [← Matrix.transpose_mul, cayleyMatrix_mul_one_add_of_isUnit hO]
  rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc,
    cayleyMatrix_mul_one_add_of_isUnit hO]
  simp only [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_one]
  noncomm_ring [orth_transpose_mul O]

/-- Exact image of the skew-symmetric Cayley chart. -/
theorem range_cayley (p : ℕ) :
    Set.range (@cayley p) =
      {O : Orth p | (1 + (O : Matrix (Fin p) (Fin p) ℝ)).det ≠ 0} := by
  ext O
  constructor
  · rintro ⟨S, rfl⟩
    exact (isUnit_det_one_add_cayleyMatrix
      (isUnit_iff_ne_zero.mpr (det_one_add_skew_ne_zero (transpose_skew S)))).ne_zero
  · intro hO
    let S : Skew p := ⟨cayleyMatrix (O : Matrix (Fin p) (Fin p) ℝ), by
      change star (cayleyMatrix (O : Matrix (Fin p) (Fin p) ℝ)) =
        -cayleyMatrix (O : Matrix (Fin p) (Fin p) ℝ)
      simpa only [Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial] using
          transpose_cayleyMatrix_of_orthogonal O (isUnit_iff_ne_zero.mpr hO)⟩
    refine ⟨S, Subtype.ext ?_⟩
    exact cayleyMatrix_cayleyMatrix (isUnit_iff_ne_zero.mpr hO)

theorem isOpen_range_cayley (p : ℕ) : IsOpen (Set.range (@cayley p)) := by
  rw [range_cayley]
  exact isOpen_ne_fun (by fun_prop) continuous_const

end Wishart.Spectral
end CanonicalSource46

section CanonicalSource47
/- Source: Wishart/SpectralCoordinates.lean -/



/-!
# Linear coordinates for the spectral chart

The upper-triangle coordinates of a symmetric matrix split into its diagonal
and a freely specified strict upper triangle. The latter is identified linearly
with a real skew-symmetric matrix. Thus eigenvalue and angle parameters occupy
one vector space of exactly the same dimension as the symmetric matrices.
-/

open Matrix TauCeti

namespace Wishart.Spectral

abbrev StrictUpper (p : ℕ) := {ij : Fin p × Fin p // ij.1 < ij.2}

/-- Strict upper entries are linear coordinates on real skew-symmetric matrices. -/
noncomputable def skewCoordinatesLinear (p : ℕ) :
    Skew p ≃ₗ[ℝ] (StrictUpper p → ℝ) where
  toFun S ij := (S : Matrix (Fin p) (Fin p) ℝ) ij.1.1 ij.1.2
  invFun a := ⟨Matrix.ofStrictUpper a, by
    change star (Matrix.ofStrictUpper a) = -Matrix.ofStrictUpper a
    simpa only [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.transpose_ofStrictUpper a⟩
  left_inv S := by
    apply Subtype.ext
    change Matrix.ofStrictUpper (fun ij : StrictUpper p =>
      (S : Matrix (Fin p) (Fin p) ℝ) ij.1.1 ij.1.2) =
        (S : Matrix (Fin p) (Fin p) ℝ)
    exact Matrix.ofStrictUpper_eq_of_transpose_eq_neg
      (fun x : ℝ => by intro h; linarith) (S : Matrix (Fin p) (Fin p) ℝ) (transpose_skew S)
  right_inv a := funext (Matrix.ofStrictUpper_apply_of_lt a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def skewCoordinates (p : ℕ) : Skew p ≃L[ℝ] (StrictUpper p → ℝ) :=
  (skewCoordinatesLinear p).toContinuousLinearEquiv

@[simp] theorem skewCoordinates_apply {p : ℕ} (S : Skew p) (ij : StrictUpper p) :
    skewCoordinates p S ij = (S : Matrix (Fin p) (Fin p) ℝ) ij.1.1 ij.1.2 := by
  simpa only [skewCoordinates, LinearEquiv.coe_toContinuousLinearEquiv'] using
    (show skewCoordinatesLinear p S ij =
      (S : Matrix (Fin p) (Fin p) ℝ) ij.1.1 ij.1.2 from rfl)

@[simp] theorem skewCoordinates_symm_apply {p : ℕ} (a : StrictUpper p → ℝ) :
    ((skewCoordinates p).symm a : Matrix (Fin p) (Fin p) ℝ) = Matrix.ofStrictUpper a := by
  simpa only [skewCoordinates, LinearEquiv.coe_toContinuousLinearEquiv_symm'] using
    (show ((skewCoordinatesLinear p).symm a : Matrix (Fin p) (Fin p) ℝ) =
      Matrix.ofStrictUpper a from rfl)

/-- The upper triangle is the disjoint union of diagonal and strict-upper indices. -/
def diagonalStrictUpperEquiv (p : ℕ) : Fin p ⊕ StrictUpper p ≃ upperTriangle p where
  toFun
    | .inl i => ⟨(i, i), le_rfl⟩
    | .inr ij => ⟨ij.1, ij.2.le⟩
  invFun ij := if h : ij.1.1 = ij.1.2 then .inl ij.1.1
    else .inr ⟨ij.1, lt_of_le_of_ne ij.2 h⟩
  left_inv := by
    intro x
    cases x with
    | inl i => simp
    | inr ij => simp [ij.property.ne]
  right_inv := by
    intro ij
    dsimp only
    split_ifs with h
    · apply Subtype.ext
      exact Prod.ext rfl h
    · rfl

@[simp] theorem diagonalStrictUpperEquiv_inl {p : ℕ} (i : Fin p) :
    diagonalStrictUpperEquiv p (.inl i) = ⟨(i, i), le_rfl⟩ := rfl

@[simp] theorem diagonalStrictUpperEquiv_inr {p : ℕ} (ij : StrictUpper p) :
    diagonalStrictUpperEquiv p (.inr ij) = ⟨ij.1, ij.2.le⟩ := rfl

/-- Split symmetric coordinates into eigenvalue and angular variables. -/
noncomputable def spectralSplit (p : ℕ) :
    Sym p ≃L[ℝ] ((Fin p → ℝ) × Skew p) :=
  (symmetricCoordinates p).trans
    ((ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : upperTriangle p => ℝ)
      (diagonalStrictUpperEquiv p)).symm.trans
      ((LinearEquiv.sumArrowLequivProdArrow (Fin p) (StrictUpper p) ℝ ℝ).toContinuousLinearEquiv.trans
        ((ContinuousLinearEquiv.refl ℝ (Fin p → ℝ)).prodCongr (skewCoordinates p).symm)))

@[simp] theorem spectralSplit_fst {p : ℕ} (X : Sym p) (i : Fin p) :
    (spectralSplit p X).1 i = (X : Matrix (Fin p) (Fin p) ℝ) i i := by
  simp only [spectralSplit, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.prodCongr_apply, ContinuousLinearEquiv.refl_apply,
    LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.sumArrowLequivProdArrow_apply_fst]
  change symmetricCoordinates p X (diagonalStrictUpperEquiv p (.inl i)) = _
  rw [diagonalStrictUpperEquiv_inl, symmetricCoordinates_apply]

@[simp] theorem spectralSplit_snd_entry {p : ℕ} (X : Sym p) (ij : StrictUpper p) :
    ((spectralSplit p X).2 : Matrix (Fin p) (Fin p) ℝ) ij.1.1 ij.1.2 =
      (X : Matrix (Fin p) (Fin p) ℝ) ij.1.1 ij.1.2 := by
  have hs : (spectralSplit p X).2 = (skewCoordinates p).symm
      (fun ab : StrictUpper p => (X : Matrix (Fin p) (Fin p) ℝ) ab.1.1 ab.1.2) := by
    simp only [spectralSplit, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.prodCongr_apply, LinearEquiv.coe_toContinuousLinearEquiv']
    congr 1
    funext ab
    rw [LinearEquiv.sumArrowLequivProdArrow_apply_snd]
    change symmetricCoordinates p X (diagonalStrictUpperEquiv p (.inr ab)) = _
    rw [diagonalStrictUpperEquiv_inr, symmetricCoordinates_apply]
  rw [hs, skewCoordinates_symm_apply, Matrix.ofStrictUpper_apply_of_lt]

/-- The spectral chart is a map between copies of the same symmetric vector space. -/
noncomputable def spectralChart {p : ℕ} (X : Sym p) : Sym p :=
  conjugate (cayley (spectralSplit p X).2) (diagonalSym (spectralSplit p X).1)

theorem continuous_spectralChart (p : ℕ) : Continuous (@spectralChart p) := by
  exact (continuous_conjugate p).comp
    (((continuous_cayley p).comp ((spectralSplit p).continuous.snd)).prodMk
      ((continuous_diagonalSym p).comp ((spectralSplit p).continuous.fst)))

end Wishart.Spectral
end CanonicalSource47

section CanonicalSource48
/- Source: Wishart/SignedCayleyCover.lean -/



open scoped Classical
open Matrix

/-!
# A finite diagonal-sign cover for Cayley spectral coordinates

The argument works for every real square matrix, not only for orthogonal ones.
The average of the signed determinants is nonzero by row multilinearity. Thus
one of the finitely many column-sign choices lies in the Cayley domain. Diagonal
signs leave diagonal spectral representatives unchanged under conjugation.
-/

namespace Wishart.Spectral

def boolSign : Bool → ℝ
  | true => 1
  | false => -1

@[simp] theorem boolSign_mul_self (b : Bool) : boolSign b * boolSign b = 1 := by
  cases b <;> norm_num [boolSign]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def signDiagonal (ε : ι → Bool) : Matrix ι ι ℝ :=
  Matrix.diagonal fun i ↦ boolSign (ε i)

@[simp] theorem signDiagonal_transpose (ε : ι → Bool) :
    (signDiagonal ε)ᵀ = signDiagonal ε := Matrix.diagonal_transpose _

@[simp] theorem signDiagonal_mul_self (ε : ι → Bool) :
    signDiagonal ε * signDiagonal ε = 1 := by
  simp only [signDiagonal, Matrix.diagonal_mul_diagonal, boolSign_mul_self,
    Matrix.diagonal_one]

theorem signDiagonal_mem_orthogonal (ε : ι → Bool) :
    signDiagonal ε ∈ Matrix.orthogonalGroup ι ℝ := by
  apply (Matrix.mem_orthogonalGroup_iff' ι ℝ).mpr
  rw [signDiagonal_transpose, signDiagonal_mul_self]

def signOrthogonal (ε : ι → Bool) : Matrix.orthogonalGroup ι ℝ :=
  ⟨signDiagonal ε, signDiagonal_mem_orthogonal ε⟩

/-- Column signs preserve a diagonal spectral matrix under orthogonal
conjugation. No positivity or distinctness of the spectrum is needed. -/
theorem signDiagonal_conjugate_diagonal (ε : ι → Bool) (lam : ι → ℝ) :
    signDiagonal ε * Matrix.diagonal lam * (signDiagonal ε)ᵀ = Matrix.diagonal lam := by
  rw [signDiagonal_transpose]
  simp only [signDiagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [mul_right_comm, boolSign_mul_self, one_mul]

/-- Exact determinant average over all choices of row signs. -/
theorem sum_det_one_add_signDiagonal_mul (A : Matrix ι ι ℝ) :
    (∑ ε : ι → Bool, (1 + signDiagonal ε * A).det) =
      (2 : ℝ) ^ Fintype.card ι := by
  let F : MultilinearMap ℝ (fun _ : ι ↦ ι → ℝ) ℝ :=
    Matrix.detRowAlternating.toMultilinearMap
  let rows (i : ι) (b : Bool) : ι → ℝ :=
    fun j ↦ (1 : Matrix ι ι ℝ) i j + boolSign b * A i j
  have hrows : (fun i ↦ ∑ b : Bool, rows i b) = (2 : ℝ) • (1 : Matrix ι ι ℝ) := by
    ext i j
    simp only [Finset.sum_apply, Fintype.sum_bool, rows, boolSign,
      Matrix.smul_apply, smul_eq_mul]
    ring
  calc
    (∑ ε : ι → Bool, (1 + signDiagonal ε * A).det) =
        ∑ ε : ι → Bool, F (fun i ↦ rows i (ε i)) := by
      apply Finset.sum_congr rfl
      intro ε hε
      change (1 + signDiagonal ε * A).det = Matrix.det (fun i j ↦ rows i (ε i) j)
      congr 1
      ext i j
      simp only [Matrix.add_apply, signDiagonal, Matrix.diagonal_mul, rows]
    _ = F (fun i ↦ ∑ b : Bool, rows i b) := (F.map_sum rows).symm
    _ = (2 : ℝ) ^ Fintype.card ι := by
      rw [hrows]
      change ((2 : ℝ) • (1 : Matrix ι ι ℝ)).det = _
      rw [Matrix.det_smul, Matrix.det_one, mul_one]

theorem exists_sign_det_one_add_left_ne_zero (A : Matrix ι ι ℝ) :
    ∃ ε : ι → Bool, (1 + signDiagonal ε * A).det ≠ 0 := by
  by_contra h
  have hzero (ε : ι → Bool) : (1 + signDiagonal ε * A).det = 0 := by
    by_contra hn
    exact h ⟨ε, hn⟩
  have hs := sum_det_one_add_signDiagonal_mul A
  simp only [hzero, Finset.sum_const_zero] at hs
  exact (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)) hs.symm

/-- Every real square matrix has a column-sign choice for which `I + A D` is
invertible. This includes both components of the orthogonal group. -/
theorem exists_sign_det_one_add_right_ne_zero (A : Matrix ι ι ℝ) :
    ∃ ε : ι → Bool, (1 + A * signDiagonal ε).det ≠ 0 := by
  obtain ⟨ε, hε⟩ := exists_sign_det_one_add_left_ne_zero Aᵀ
  refine ⟨ε, ?_⟩
  rw [← Matrix.det_transpose, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_mul, signDiagonal_transpose]
  exact hε

theorem exists_sign_for_cayley (O : Matrix.orthogonalGroup ι ℝ) :
    ∃ ε : ι → Bool,
      (1 + ((O * signOrthogonal ε : Matrix.orthogonalGroup ι ℝ) : Matrix ι ι ℝ)).det ≠ 0 := by
  simpa only [Submonoid.coe_mul, signOrthogonal] using
    exists_sign_det_one_add_right_ne_zero (O : Matrix ι ι ℝ)

end Wishart.Spectral
end CanonicalSource48

section CanonicalSource49
/- Source: Wishart/SpectralSurjectivity.lean -/



/-!
# Global coverage by Cayley spectral coordinates

Column signs commute with diagonal spectral representatives. The finite sign
cover therefore places every symmetric matrix, including matrices with repeated
eigenvalues, in the image of the global Cayley spectral map. This will let the
zero-Jacobian image theorem handle repeated spectra without a discriminant.
-/

open Matrix

namespace Wishart.Spectral

theorem conjugate_signOrthogonal_diagonal {p : ℕ}
    (ε : Fin p → Bool) (lam : Fin p → ℝ) :
    conjugate (signOrthogonal ε) (diagonalSym lam) = diagonalSym lam := by
  apply Subtype.ext
  simpa only [conjugate, Matrix.coe_symmetricCongruenceLinearMap_apply,
    diagonalSym, signOrthogonal] using signDiagonal_conjugate_diagonal ε lam

/-- Every fixed spectral representative can use a Cayley frame after changing
column signs. The spectrum is preserved literally. -/
theorem exists_cayley_conjugate_diagonal {p : ℕ} (S : Sym p) :
    ∃ A : Skew p, conjugate (cayley A) (diagonalSym (coordinateSpectrum S)) = S := by
  obtain ⟨O, hO⟩ := exists_conjugate_diagonal_spectrum S
  obtain ⟨ε, hε⟩ := exists_sign_for_cayley O
  have hmem : O * signOrthogonal ε ∈ Set.range (@cayley p) := by
    rw [range_cayley]
    exact hε
  obtain ⟨A, hA⟩ := hmem
  refine ⟨A, ?_⟩
  rw [hA, conjugate_mul, conjugate_signOrthogonal_diagonal]
  exact hO

theorem exists_spectralChart_preimage_with_spectrum {p : ℕ} (S : Sym p) :
    ∃ X : Sym p, spectralChart X = S ∧
      (spectralSplit p X).1 = coordinateSpectrum S := by
  obtain ⟨A, hA⟩ := exists_cayley_conjugate_diagonal S
  refine ⟨(spectralSplit p).symm (coordinateSpectrum S, A), ?_, ?_⟩
  · simpa only [spectralChart, ContinuousLinearEquiv.apply_symm_apply] using hA
  · simp only [ContinuousLinearEquiv.apply_symm_apply]

theorem spectralChart_surjective (p : ℕ) : Function.Surjective (@spectralChart p) := by
  intro S
  obtain ⟨X, hX, _⟩ := exists_spectralChart_preimage_with_spectrum S
  exact ⟨X, hX⟩

theorem repeated_spectrum_subset_spectralChart_image (p : ℕ) :
    {S : Sym p | ¬Function.Injective (coordinateSpectrum S)} ⊆
      spectralChart '' {X : Sym p | ¬Function.Injective (spectralSplit p X).1} := by
  intro S hS
  obtain ⟨X, hX, hspec⟩ := exists_spectralChart_preimage_with_spectrum S
  refine ⟨X, ?_, hX⟩
  change ¬Function.Injective (spectralSplit p X).1
  rw [hspec]
  exact hS

end Wishart.Spectral
end CanonicalSource49

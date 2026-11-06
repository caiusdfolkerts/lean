module

public import wishart.verified.finite_order_growth
public import wishart.verified.finite_order_integral

@[expose] public section

/-!
# Radial generator calculus with exactly two derivatives

These identities use finite-order differentiability.  Their continuity and
polynomial bounds involve only the value, differential, and Hessian; no third
derivative is introduced when averaging the generator.
-/

noncomputable section

open Matrix MeasureTheory Set WishartVerification
open scoped Classical BigOperators Matrix.Norms.Operator

namespace Wishart.FiniteOrder

section Products

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_product_apply_c1 {f g : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (X H : E) :
    fderiv ℝ (fun Y => f Y * g Y) X H =
      f X * fderiv ℝ g X H + g X * fderiv ℝ f X H := by
  rw [fderiv_fun_mul (hf.differentiable (by norm_num) X)
    (hg.differentiable (by norm_num) X)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem contDiff_fderiv_apply_c2 {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (H : E) :
    ContDiff ℝ 1 (fun Y => fderiv ℝ f Y H) := by
  have hd := (contDiff_succ_iff_fderiv.mp (show ContDiff ℝ (1 + 1) f from hf)).2.2
  exact hd.clm_apply contDiff_const

set_option backward.isDefEq.respectTransparency false in
theorem second_fderiv_product_apply_c2 {f g : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (X H K : E) :
    fderiv ℝ (fun Y => fderiv ℝ (fun Z => f Z * g Z) Y H) X K =
      f X * fderiv ℝ (fun Y => fderiv ℝ g Y H) X K +
      g X * fderiv ℝ (fun Y => fderiv ℝ f Y H) X K +
      fderiv ℝ f X K * fderiv ℝ g X H + fderiv ℝ g X K * fderiv ℝ f X H := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have hdf := contDiff_fderiv_apply_c2 hf H
  have hdg := contDiff_fderiv_apply_c2 hg H
  have heq : (fun Y => fderiv ℝ (fun Z => f Z * g Z) Y H) =
      fun Y => f Y * fderiv ℝ g Y H + g Y * fderiv ℝ f Y H :=
    funext fun Y => fderiv_product_apply_c1 hf1 hg1 Y H
  have hleft : DifferentiableAt ℝ (fun Y => f Y * fderiv ℝ g Y H) X :=
    (hf1.differentiable (by norm_num) X).mul (hdg.differentiable (by norm_num) X)
  have hright : DifferentiableAt ℝ (fun Y => g Y * fderiv ℝ f Y H) X :=
    (hg1.differentiable (by norm_num) X).mul (hdf.differentiable (by norm_num) X)
  rw [heq, fderiv_fun_add hleft hright]
  simp only [ContinuousLinearMap.add_apply, fderiv_product_apply_c1 hf1 hdg,
    fderiv_product_apply_c1 hg1 hdf]
  ring

theorem fderiv_fderiv_apply_c2 {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (X H K : E) :
    fderiv ℝ (fderiv ℝ f) X K H = fderiv ℝ (fun Y => fderiv ℝ f Y H) X K := by
  have hd := (contDiff_succ_iff_fderiv.mp (show ContDiff ℝ (1 + 1) f from hf)).2.2
  have h := (hd.differentiable (by norm_num) X).hasFDerivAt
  rw [(h.clm_apply (hasFDerivAt_const H X)).fderiv]
  simp

theorem continuous_fderiv_fderiv_c2 {f : E → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (fderiv ℝ (fderiv ℝ f)) := by
  exact ((contDiff_succ_iff_fderiv.mp
    (show ContDiff ℝ (1 + 1) f from hf)).2.2).continuous_fderiv (by norm_num)

theorem continuous_hessian_apply_c2 {f : E → ℝ} (hf : ContDiff ℝ 2 f) (H K : E) :
    Continuous (fun X => fderiv ℝ (fderiv ℝ f) X K H) :=
  ((continuous_fderiv_fderiv_c2 hf).clm_apply continuous_const).clm_apply continuous_const

theorem polynomial_hessian_apply_c2 {S : Set E} {f : E → ℝ}
    (hf : C2PolynomialOn S f) (H K : E) :
    PolynomialBoundOn S (fun X => fderiv ℝ (fderiv ℝ f) X K H) :=
  (hf.second.clm_apply (PolynomialBoundOn.const _ K)).clm_apply (PolynomialBoundOn.const _ H)

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem c1_fderiv_comp_apply {S : Set E} {T : Set D} {f : E → ℝ}
    (hf : C2PolynomialOn S f) {P H : D → E}
    (hP : C1PolynomialOn T P) (hPS : MapsTo P T S) (hH : C1PolynomialOn T H) :
    C1PolynomialOn T (fun x => fderiv ℝ f (P x) (H x)) :=
  (hf.fderiv.comp hP hPS).clm_apply hH

theorem polynomial_hessian_comp_apply {S : Set E} {T : Set D} {f : E → ℝ}
    (hf : C2PolynomialOn S f) {P H K : D → E}
    (hP : PolynomialBoundOn T P) (hPS : MapsTo P T S)
    (hH : PolynomialBoundOn T H) (hK : PolynomialBoundOn T K) :
    PolynomialBoundOn T (fun x => fderiv ℝ (fderiv ℝ f) (P x) (H x) (K x)) :=
  ((hf.second.comp hP hPS).clm_apply hH).clm_apply hK

theorem continuous_hessian_comp_apply {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    {P H K : D → E} (hP : Continuous P) (hH : Continuous H) (hK : Continuous K) :
    Continuous (fun x => fderiv ℝ (fderiv ℝ f) (P x) (H x) (K x)) :=
  (((continuous_fderiv_fderiv_c2 hf).comp hP).clm_apply hH).clm_apply hK

theorem hasDerivAt_fderiv_apply_curve_c2 {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    {P H : ℝ → E} {P' H' : E} {t : ℝ}
    (hP : HasDerivAt P P' t) (hH : HasDerivAt H H' t) :
    HasDerivAt (fun s => fderiv ℝ f (P s) (H s))
      (fderiv ℝ (fderiv ℝ f) (P t) P' (H t) + fderiv ℝ f (P t) H') t := by
  have hd := (contDiff_succ_iff_fderiv.mp (show ContDiff ℝ (1 + 1) f from hf)).2.2
  have h := (hd.differentiable (by norm_num) (P t)).hasFDerivAt.comp_hasDerivAt t hP
  simpa only [Function.comp_def, add_comm] using h.clm_apply hH

end Products

variable {p : ℕ}

theorem symmetricSecondDerivative_eq_c2 {f : SymmetricMatrix p → ℝ}
    (hf : ContDiff ℝ 2 f) (X H K : SymmetricMatrix p) :
    symmetricSecondDerivative f X H K =
      fderiv ℝ (fun Y => fderiv ℝ f Y H) X K := by
  exact fderiv_fderiv_apply_c2 hf X H K

theorem symmetricRadialGenerator_eq_directional_c2 {f : SymmetricMatrix p → ℝ}
    (hf : ContDiff ℝ 2 f) (N : ℝ) (v : EuclideanSpace ℝ (Fin p))
    (X : SymmetricMatrix p) :
    symmetricRadialGenerator N v f X = symmetricDirectionalGenerator N v f X := by
  simp only [symmetricRadialGenerator, symmetricDirectionalGenerator,
    radialCovarianceContraction, symmetricSecondDerivative_eq_c2 hf]

theorem c1_radialDerivativeTest {S : Set (SymmetricMatrix p)}
    {f : SymmetricMatrix p → ℝ} (hf : C2PolynomialOn S f)
    (v : EuclideanSpace ℝ (Fin p)) (i : Fin p) :
    C1PolynomialOn S (radialDerivativeTest f v i) :=
  hf.fderiv.clm_apply (C1PolynomialOn.const _ (symmetricRankDirection v (coordinateVector i)))

theorem continuous_symmetricRadialGenerator_c2 {f : SymmetricMatrix p → ℝ}
    (hf : ContDiff ℝ 2 f) (N : ℝ) (v : EuclideanSpace ℝ (Fin p)) :
    Continuous (symmetricRadialGenerator N v f) := by
  have hd := hf.continuous_fderiv (by norm_num)
  unfold symmetricRadialGenerator radialCovarianceContraction symmetricSecondDerivative
  apply Continuous.add
  · exact continuous_const.mul (hd.clm_apply continuous_const)
  · apply continuous_finsetSum
    intro i hi
    apply continuous_finsetSum
    intro j hj
    have hentry : Continuous (fun X : SymmetricMatrix p =>
        (X : Matrix (Fin p) (Fin p) ℝ) i j) := by
      exact (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
    exact hentry.mul (continuous_hessian_apply_c2 hf
      (symmetricRankDirection v (coordinateVector i))
      (symmetricRankDirection v (coordinateVector j)))

theorem polynomial_symmetricRadialGenerator_c2 {S : Set (SymmetricMatrix p)}
    {f : SymmetricMatrix p → ℝ} (hf : C2PolynomialOn S f)
    (N : ℝ) (v : EuclideanSpace ℝ (Fin p)) :
    PolynomialBoundOn S (symmetricRadialGenerator N v f) := by
  have hentry (i j : Fin p) : PolynomialBoundOn S
      (fun X : SymmetricMatrix p => (X : Matrix (Fin p) (Fin p) ℝ) i j) := by
    let L : SymmetricMatrix p →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
      ((Matrix.entryLinearMap ℝ ℝ i j).comp
        (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)).subtype)
    exact PolynomialBoundOn.of_temperate L.hasTemperateGrowth
  change PolynomialBoundOn S (fun X =>
    2 * N * fderiv ℝ f X (rankOneSymmetric v) +
      ∑ i, ∑ j, (X : Matrix (Fin p) (Fin p) ℝ) i j *
        fderiv ℝ (fderiv ℝ f) X (symmetricRankDirection v (coordinateVector j))
          (symmetricRankDirection v (coordinateVector i)))
  apply PolynomialBoundOn.add
  · exact (PolynomialBoundOn.const _ (2 * N)).mul
      (hf.derivative.clm_apply (PolynomialBoundOn.const _ (rankOneSymmetric v)))
  · apply PolynomialBoundOn.finset_sum
    intro i hi
    apply PolynomialBoundOn.finset_sum
    intro j hj
    exact (hentry i j).mul (polynomial_hessian_apply_c2 hf
      (symmetricRankDirection v (coordinateVector i))
      (symmetricRankDirection v (coordinateVector j)))

theorem c1_radialIntegrand {f : SymmetricMatrix p → ℝ}
    (hf : C2PolynomialOn (psdCone p) f) (v : EuclideanSpace ℝ (Fin p)) :
    C1PolynomialOn (univ ×ˢ radialSupport p)
      (fun z : ℝ × RadialInputSpace p => f (radialInput v z.1 z.2)) :=
  hf.toC1.comp (C1PolynomialOn.of_temperate (hasTemperateGrowth_radialInput v))
    (radialInput_parameter_mapsTo v)

theorem c1_radialFirstIntegrand {f : SymmetricMatrix p → ℝ}
    (hf : C2PolynomialOn (psdCone p) f) (v : EuclideanSpace ℝ (Fin p)) :
    C1PolynomialOn (univ ×ˢ radialSupport p)
      (fun z : ℝ × RadialInputSpace p => radialFirstIntegrand f v z.1 z.2) :=
  c1_fderiv_comp_apply hf
    (C1PolynomialOn.of_temperate (hasTemperateGrowth_radialInput v))
    (radialInput_parameter_mapsTo v)
    (C1PolynomialOn.of_temperate (hasTemperateGrowth_radialDirection v))

theorem continuous_radialSecondIntegrand_c2 {f : SymmetricMatrix p → ℝ}
    (hf : ContDiff ℝ 2 f) (v : EuclideanSpace ℝ (Fin p)) :
    Continuous (fun z : ℝ × RadialInputSpace p => radialSecondIntegrand f v z.1 z.2) := by
  have hP := (hasTemperateGrowth_radialInput v).1.continuous
  have hH := (hasTemperateGrowth_radialDirection v).1.continuous
  exact (continuous_hessian_comp_apply hf hP hH hH).add
    (continuous_const.mul (((hf.continuous_fderiv (by norm_num)).comp hP).clm_apply
      continuous_const))

theorem polynomial_radialSecondIntegrand_c2 {f : SymmetricMatrix p → ℝ}
    (hf : C2PolynomialOn (psdCone p) f) (v : EuclideanSpace ℝ (Fin p)) :
    PolynomialBoundOn (univ ×ˢ radialSupport p)
      (fun z : ℝ × RadialInputSpace p => radialSecondIntegrand f v z.1 z.2) := by
  have hP : PolynomialBoundOn (univ ×ˢ radialSupport p)
      (fun z : ℝ × RadialInputSpace p => radialInput v z.1 z.2) :=
    PolynomialBoundOn.of_temperate (hasTemperateGrowth_radialInput v)
  have hH : PolynomialBoundOn (univ ×ˢ radialSupport p)
      (fun z : ℝ × RadialInputSpace p => radialDirection v z.1 z.2) :=
    PolynomialBoundOn.of_temperate (hasTemperateGrowth_radialDirection v)
  exact (polynomial_hessian_comp_apply hf hP (radialInput_parameter_mapsTo v) hH hH).add
    ((PolynomialBoundOn.const _ 2).mul
      ((hf.derivative.comp hP (radialInput_parameter_mapsTo v)).clm_apply
        (PolynomialBoundOn.const _ (rankOneSymmetric v))))

theorem hasDerivAt_radialIntegrand_c2 {f : SymmetricMatrix p → ℝ}
    (hf : ContDiff ℝ 2 f) (v : EuclideanSpace ℝ (Fin p))
    (Y : RadialInputSpace p) (r : ℝ) :
    HasDerivAt (fun s => f (radialInput v s Y)) (radialFirstIntegrand f v r Y) r :=
  (hf.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt r
    (hasDerivAt_radialInput v Y r)

theorem hasDerivAt_radialFirstIntegrand_c2 {f : SymmetricMatrix p → ℝ}
    (hf : ContDiff ℝ 2 f) (v : EuclideanSpace ℝ (Fin p))
    (Y : RadialInputSpace p) (r : ℝ) :
    HasDerivAt (fun s => radialFirstIntegrand f v s Y)
      (radialSecondIntegrand f v r Y) r := by
  have h := hasDerivAt_fderiv_apply_curve_c2 hf
    (hasDerivAt_radialInput v Y r) (hasDerivAt_radialDirection v Y r)
  simpa [radialFirstIntegrand, radialSecondIntegrand, smul_eq_mul] using h

/- The diagonal-test product formula follows below. -/
set_option backward.isDefEq.respectTransparency false in
theorem symmetricRadialGenerator_diagonal_test_c2 {p : ℕ}
    {φ : ℝ → ℝ} (hφ : φ.HasTemperateGrowth)
    {f : SymmetricMatrix p → ℝ} (hf : ContDiff ℝ 2 f)
    (N : ℝ) (a : Fin p) (X : SymmetricMatrix p) :
    symmetricRadialGenerator N (coordinateVector a)
        (fun Y => φ (diagonalEntryCLM a Y) * f Y) X =
      φ (diagonalEntryCLM a X) * symmetricRadialGenerator N (coordinateVector a) f X +
        (4 * diagonalEntryCLM a X * deriv (deriv φ) (diagonalEntryCLM a X) +
          2 * N * deriv φ (diagonalEntryCLM a X)) * f X +
        4 * deriv φ (diagonalEntryCLM a X) *
          fderiv ℝ f X
            (congruenceVelocity (outerMatrix (coordinateVector a) (coordinateVector a)) X) := by
  have htest : (fun Y => φ (diagonalEntryCLM a Y)).HasTemperateGrowth := by
    simpa only [Function.comp_def] using hφ.comp (diagonalEntryCLM a).hasTemperateGrowth
  have ht2 : ContDiff ℝ 2 (fun Y => φ (diagonalEntryCLM a Y)) := htest.1.of_le (by simp)
  have ht1 : ContDiff ℝ 1 (fun Y => φ (diagonalEntryCLM a Y)) := htest.1.of_le (by simp)
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hproduct : ContDiff ℝ 2 (fun Y => φ (diagonalEntryCLM a Y) * f Y) := ht2.mul hf
  rw [symmetricRadialGenerator_eq_directional_c2 hproduct,
    symmetricRadialGenerator_eq_directional_c2 hf]
  unfold symmetricDirectionalGenerator
  simp_rw [second_fderiv_product_apply_c2 ht2 hf]
  simp_rw [second_fderiv_scalar_linear_apply hφ]
  simp only [fderiv_product_apply_c1 ht1 hf1, fderiv_scalar_linear_apply hφ,
    diagonalEntry_rankOne_coordinate, diagonalEntry_direction_coordinate,
    mul_one, mul_add, Finset.sum_add_distrib]
  have hX := (selfAdjoint.isHermitian_coe X).isSymm
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_const_zero, Finset.sum_ite_irrel,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_one]
  simp_rw [show ∀ i, (X : Matrix (Fin p) (Fin p) ℝ) i a =
      (X : Matrix (Fin p) (Fin p) ℝ) a i from fun i => (hX.apply i a).symm]
  have hdouble (c : ℝ) (H : Fin p → Fin p → ℝ) :
      (∑ i, ∑ j, (X : Matrix (Fin p) (Fin p) ℝ) i j * (c * H i j)) =
        c * ∑ i, ∑ j, (X : Matrix (Fin p) (Fin p) ℝ) i j * H i j := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hleft (c : ℝ) (D : Fin p → ℝ) :
      (∑ i, (X : Matrix (Fin p) (Fin p) ℝ) a i * (c * D i)) =
        c * ∑ i, (X : Matrix (Fin p) (Fin p) ℝ) a i * D i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hright (c : ℝ) (D : Fin p → ℝ) :
      (∑ i, (X : Matrix (Fin p) (Fin p) ℝ) a i * D i * c) =
        c * ∑ i, (X : Matrix (Fin p) (Fin p) ℝ) a i * D i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simp only [hdouble, hleft, hright, coordinate_drift_sum, diagonalEntryCLM_apply]
  have hscaled (c : ℝ) (D : Fin p → ℝ) :
      (∑ i, c * (X : Matrix (Fin p) (Fin p) ℝ) a i * D i * 2) =
        2 * c * ∑ i, (X : Matrix (Fin p) (Fin p) ℝ) a i * D i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  ring_nf
  rw [hscaled, coordinate_drift_sum]
  ring


end Wishart.FiniteOrder

end

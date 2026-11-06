module

public import wishart.verified.finite_order_radial_calculus
public import wishart.verified.finite_order_covariance
public import tau_ceti.analysis.calculus.second_derivative

/-!
# Covariance congruence for the finite-order radial generator

The chain rule transports the differential and Hessian through an arbitrary
rectangular congruence. On the positive semidefinite cone, a covariance is a
finite sum of rank-one matrices; this transports the covariance contraction
without choosing coordinates for a Hessian trace. Only two derivatives of the
test are used.
-/

@[expose] public section

noncomputable section

open Matrix MeasureTheory Set WishartVerification
open scoped Classical BigOperators RealInnerProductSpace Matrix.Norms.Operator

namespace Wishart.FiniteOrder

section ChainRule

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fderiv_comp_clm_c2 (L : E →L[ℝ] F) {f : F → ℝ}
    (hf : ContDiff ℝ 2 f) (X H : E) :
    fderiv ℝ (fun Y => f (L Y)) X H = fderiv ℝ f (L X) (L H) := by
  have hd := ((hf.differentiable (by norm_num) (L X)).hasFDerivAt.comp X L.hasFDerivAt).fderiv
  exact congrArg (fun A : E →L[ℝ] ℝ => A H) hd

theorem hessian_comp_clm_c2 (L : E →L[ℝ] F) {f : F → ℝ}
    (hf : ContDiff ℝ 2 f) (X H K : E) :
    fderiv ℝ (fderiv ℝ (fun Y => f (L Y))) X K H =
      fderiv ℝ (fderiv ℝ f) (L X) (L K) (L H) := by
  have h := TauCeti.fderiv_fderiv_comp_apply (b := X) hf.contDiffAt L.contDiff.contDiffAt K H
  have hD : fderiv ℝ (L : E → F) = fun _ => L := by
    funext Y
    exact L.fderiv
  rw [hD] at h
  simpa only [Function.comp_def, ContinuousLinearMap.fderiv, fderiv_const_apply,
    ContinuousLinearMap.zero_apply, map_zero, add_zero] using h

end ChainRule

theorem symmetricCongruence_mapsTo_psdCone {p r : ℕ}
    (L : Matrix (Fin p) (Fin r) ℝ) :
    MapsTo (Matrix.symmetricCongruenceLinearMap L).toContinuousLinearMap
      (psdCone r) (psdCone p) := by
  intro X hX
  simpa only [psdCone, mem_setOf_eq, LinearMap.coe_toContinuousLinearMap',
    Matrix.coe_symmetricCongruenceLinearMap_apply,
    Matrix.conjTranspose_eq_transpose_of_trivial] using
    (show (X : Matrix (Fin r) (Fin r) ℝ).PosSemidef from hX).mul_mul_conjTranspose_same L

theorem C2PolynomialOn.symmetricCongruence {p r : ℕ}
    {f : SymmetricMatrix p → ℝ} (hf : C2PolynomialOn (psdCone p) f)
    (L : Matrix (Fin p) (Fin r) ℝ) :
    C2PolynomialOn (psdCone r) (fun X => f (Matrix.symmetricCongruenceLinearMap L X)) :=
  hf.comp_linear (Matrix.symmetricCongruenceLinearMap L).toContinuousLinearMap
    (symmetricCongruence_mapsTo_psdCone L)

theorem symmetricCongruence_symmetricRankDirection {p r : ℕ}
    (L : Matrix (Fin p) (Fin r) ℝ) (v w : EuclideanSpace ℝ (Fin r)) :
    Matrix.symmetricCongruenceLinearMap L (symmetricRankDirection v w) =
      symmetricRankDirection (L.toEuclideanLin v) (L.toEuclideanLin w) := by
  apply Subtype.ext
  rw [Matrix.coe_symmetricCongruenceLinearMap_apply,
    coe_symmetricRankDirection, coe_symmetricRankDirection]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
  rfl

/-- The covariance of a rectangular matrix is the sum of its column outer products. -/
theorem sum_rankOneSymmetric_columns {p r : ℕ} (A : Matrix (Fin p) (Fin r) ℝ) :
    (((∑ k : Fin r, rankOneSymmetric (WithLp.toLp 2 (fun i => A i k))) :
      SymmetricMatrix p) : Matrix (Fin p) (Fin p) ℝ) = A * Aᵀ := by
  rw [Submodule.coe_sum]
  ext i j
  simp only [Matrix.sum_apply, coe_rankOneSymmetric, Matrix.vecMulVec_apply,
    WithLp.ofLp_toLp, Matrix.mul_apply, Matrix.transpose_apply]

theorem radialCovarianceContraction_finset_sum {p : ℕ} {ι : Type*}
    (f : SymmetricMatrix p → ℝ) (X : SymmetricMatrix p)
    (v : EuclideanSpace ℝ (Fin p)) (s : Finset ι)
    (B : ι → Matrix (Fin p) (Fin p) ℝ) :
    radialCovarianceContraction f X v (∑ i ∈ s, B i) =
      ∑ i ∈ s, radialCovarianceContraction f X v (B i) := by
  induction s using Finset.induction_on with
  | empty => simp [radialCovarianceContraction]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, radialCovarianceContraction_add, ih]

/-- The radial generator is natural under rectangular covariance congruence
at every positive semidefinite matrix, including singular matrices. -/
theorem symmetricRadialGenerator_congruence_c2 {p r : ℕ}
    (L : Matrix (Fin p) (Fin r) ℝ) (N : ℝ) (v : EuclideanSpace ℝ (Fin r))
    {f : SymmetricMatrix p → ℝ} (hf : ContDiff ℝ 2 f)
    (X : SymmetricMatrix r) (hX : (X : Matrix (Fin r) (Fin r) ℝ).PosSemidef) :
    symmetricRadialGenerator N v
        (fun Y => f (Matrix.symmetricCongruenceLinearMap L Y)) X =
      symmetricRadialGenerator N (L.toEuclideanLin v) f
        (Matrix.symmetricCongruenceLinearMap L X) := by
  let Φ := (Matrix.symmetricCongruenceLinearMap L).toContinuousLinearMap
  let A := eigenGaussianMatrix hX
  let w : Fin r → EuclideanSpace ℝ (Fin r) := fun k => WithLp.toLp 2 (fun i => A i k)
  have hXsum : X = ∑ k, rankOneSymmetric (w k) := by
    apply Subtype.ext
    exact (eigenGaussianMatrix_covariance hX).symm.trans
      (sum_rankOneSymmetric_columns A).symm
  have hΦsum : Φ X = ∑ k, rankOneSymmetric (L.toEuclideanLin (w k)) := by
    rw [hXsum, map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact Wishart.symmetricCongruence_rankOne L (w k)
  have hsecond (H K : SymmetricMatrix r) :
      symmetricSecondDerivative (fun Y => f (Φ Y)) X H K =
        symmetricSecondDerivative f (Φ X) (Φ H) (Φ K) :=
    hessian_comp_clm_c2 Φ hf X H K
  have hdir (z : EuclideanSpace ℝ (Fin r)) :
      Φ (symmetricRankDirection v z) =
        symmetricRankDirection (L.toEuclideanLin v) (L.toEuclideanLin z) :=
    symmetricCongruence_symmetricRankDirection L v z
  have hfirst : fderiv ℝ (fun Y => f (Φ Y)) X (rankOneSymmetric v) =
      fderiv ℝ f (Φ X) (rankOneSymmetric (L.toEuclideanLin v)) := by
    rw [fderiv_comp_clm_c2 Φ hf]
    exact congrArg (fderiv ℝ f (Φ X)) (Wishart.symmetricCongruence_rankOne L v)
  have hcovX : (X : Matrix (Fin r) (Fin r) ℝ) =
      ∑ k, (rankOneSymmetric (w k) : Matrix (Fin r) (Fin r) ℝ) := by
    simpa only [Submodule.coe_sum] using congrArg
      (fun Z : SymmetricMatrix r => (Z : Matrix (Fin r) (Fin r) ℝ)) hXsum
  have hcovΦ : (Φ X : Matrix (Fin p) (Fin p) ℝ) =
      ∑ k, (rankOneSymmetric (L.toEuclideanLin (w k)) : Matrix (Fin p) (Fin p) ℝ) := by
    simpa only [Submodule.coe_sum] using congrArg
      (fun Z : SymmetricMatrix p => (Z : Matrix (Fin p) (Fin p) ℝ)) hΦsum
  have hcov : radialCovarianceContraction (fun Y => f (Φ Y)) X v
      (X : Matrix (Fin r) (Fin r) ℝ) =
      radialCovarianceContraction f (Φ X) (L.toEuclideanLin v)
        (Φ X : Matrix (Fin p) (Fin p) ℝ) := by
    calc
      _ = radialCovarianceContraction (fun Y => f (Φ Y)) X v
          (∑ k, (rankOneSymmetric (w k) : Matrix (Fin r) (Fin r) ℝ)) :=
        congrArg (radialCovarianceContraction (fun Y => f (Φ Y)) X v) hcovX
      _ = ∑ k, radialCovarianceContraction (fun Y => f (Φ Y)) X v
          (rankOneSymmetric (w k) : Matrix (Fin r) (Fin r) ℝ) :=
        radialCovarianceContraction_finset_sum _ _ _ Finset.univ _
      _ = ∑ k, radialCovarianceContraction f (Φ X) (L.toEuclideanLin v)
          (rankOneSymmetric (L.toEuclideanLin (w k)) : Matrix (Fin p) (Fin p) ℝ) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [radialCovarianceContraction_rankOne, radialCovarianceContraction_rankOne,
          hsecond, hdir]
      _ = radialCovarianceContraction f (Φ X) (L.toEuclideanLin v)
          (∑ k, (rankOneSymmetric (L.toEuclideanLin (w k)) : Matrix (Fin p) (Fin p) ℝ)) :=
        (radialCovarianceContraction_finset_sum _ _ _ Finset.univ _).symm
      _ = _ := congrArg (radialCovarianceContraction f (Φ X) (L.toEuclideanLin v)) hcovΦ.symm
  change 2 * N * fderiv ℝ (fun Y => f (Φ Y)) X (rankOneSymmetric v) +
    radialCovarianceContraction (fun Y => f (Φ Y)) X v (X : Matrix (Fin r) (Fin r) ℝ) =
      2 * N * fderiv ℝ f (Φ X) (rankOneSymmetric (L.toEuclideanLin v)) +
        radialCovarianceContraction f (Φ X) (L.toEuclideanLin v)
          (Φ X : Matrix (Fin p) (Fin p) ℝ)
  rw [hfirst, hcov]

end Wishart.FiniteOrder

end

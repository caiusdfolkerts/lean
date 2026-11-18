module

public import Mathlib

/-! # Ellipsoid reconstruction and quantitative recovery

The statements below retain the literal Euclidean bodies and parallel-body
Lebesgue volumes of the source development. All project-specific definitions
needed to read the claims are copied here with their original values.
The paper is `paper.pdf`; the entry covers Theorems 1.1, 1.2, 2.1 and the
measured coefficient bounds in Section 5.1. No novelty or independent review
is asserted by this packaging.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Polynomial Filter Topology Matrix
open scoped BigOperators Pointwise ContDiff Manifold
namespace EllipsoidVerification

/-- Euclidean n-space with its usual inner product. -/
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Lebesgue volume of the Euclidean unit ball. -/
def unitBallVolume (n : ℕ) : ℝ :=
  (volume (Metric.closedBall (0 : Space n) 1)).toReal

/-- Minkowski sum with a closed ball of radius r. -/
def parallelBody {n : ℕ} (K : Set (Space n)) (r : ℝ) : Set (Space n) :=
  K + Metric.closedBall 0 r

/-- Actual Lebesgue volume of the parallel body. -/
def parallelVolume {n : ℕ} (K : Set (Space n)) (r : ℝ) : ℝ :=
  (volume (parallelBody K r)).toReal

/-- Polynomial interpolating the n+1 parallel-body volumes at the integers 0 through n. -/
def steinerInterpolant {n : ℕ} (K : Set (Space n)) : ℝ[X] :=
  Lagrange.interpolate Finset.univ (fun i : Fin (n + 1) => (i.val : ℝ))
    (fun i => parallelVolume K i.val)

/-- Normalized Steiner coefficient, obtained from actual parallel-body volumes. -/
def intrinsicVolume {n : ℕ} (K : Set (Space n)) (k : ℕ) : ℝ :=
  if k ≤ n then (steinerInterpolant K).coeff (n - k) / unitBallVolume (n - k) else 0

/-- Diagonal coordinate scaling by the semiaxes. -/
def axisMap {n : ℕ} (a : Fin n → ℝ) (x : Space n) : Space n :=
  WithLp.toLp 2 (fun i => a i * x i)

/-- A center, an orthogonal frame, and strictly positive semiaxes; repetitions are allowed. -/
structure FullEllipsoid (n : ℕ) where
  center : Space n
  frame : Space n ≃ₗᵢ[ℝ] Space n
  semiaxis : Fin n → ℝ
  semiaxis_pos : ∀ i, 0 < semiaxis i

namespace FullEllipsoid

/-- The image of the actual closed unit ball by the ellipsoid parameterization. -/
def body {n : ℕ} (E : FullEllipsoid n) : Set (Space n) :=
  (fun x => E.center + E.frame (axisMap E.semiaxis x)) '' Metric.closedBall 0 1

/-- Intrinsic volume of this ellipsoid as a literal Euclidean set. -/
def volume {n : ℕ} (E : FullEllipsoid n) (k : ℕ) : ℝ :=
  intrinsicVolume E.body k

/-- All semiaxes lie in the interval [a,b]. -/
def axesIn {n : ℕ} (E : FullEllipsoid n) (a b : ℝ) : Prop :=
  ∀ i, a ≤ E.semiaxis i ∧ E.semiaxis i ≤ b

/-- The two Euclidean sets differ by an isometry. -/
def congruent {n : ℕ} (E F : FullEllipsoid n) : Prop :=
  ∃ T : Space n ≃ᵢ Space n, T '' E.body = F.body

/-- Minimum over permutations of the maximum discrepancy of semiaxes. -/
def axisDistance {n : ℕ} (E F : FullEllipsoid n) : ℝ :=
  ⨅ σ : Equiv.Perm (Fin n), ⨆ i : Fin n, |E.semiaxis i - F.semiaxis (σ i)|

/-- Maximum discrepancy of the first n intrinsic volumes. -/
def volumeDistance {n : ℕ} (E F : FullEllipsoid n) : ℝ :=
  ⨆ k : Fin n, |E.volume (k.val + 1) - F.volume (k.val + 1)|

end FullEllipsoid

/-- Theorem 1.1: equality of all positive-degree intrinsic volumes implies Euclidean congruence. -/
def IntrinsicReconstruction : Prop :=
  ∀ (n : ℕ) (E F : FullEllipsoid n),
    (∀ k : ℕ, 1 ≤ k → k ≤ n → E.volume k = F.volume k) → E.congruent F

/-- Theorem 1.2: a uniform two-point Holder estimate with exponent 1/n on bounded nondegenerate families. -/
def UniformHolderRecovery : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ a b : ℝ, 0 < a → a ≤ b →
    ∃ C : ℝ, 0 < C ∧ ∀ E F : FullEllipsoid n,
      E.axesIn a b → F.axesIn a b →
      E.axisDistance F ≤ C * Real.rpow (E.volumeDistance F) (1 / (n : ℝ))

/-- Theorem 1.2: every larger exponent fails in every positive semiaxis neighborhood of an interior sphere. -/
def SharpHolderRecovery : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ a b r : ℝ, 0 < a → a < r → r < b →
    ∀ γ : ℝ, 1 / (n : ℝ) < γ → ∀ δ C : ℝ, 0 < δ → 0 < C →
      ∃ E F : FullEllipsoid n,
        E.axesIn a b ∧ F.axesIn a b ∧
        (∀ i, |E.semiaxis i - r| < δ) ∧
        (∀ i, |F.semiaxis i - r| < δ) ∧
        C * Real.rpow (E.volumeDistance F) γ < E.axisDistance F

/-- The equal-volume sharpness clause for every n at least two. -/
def SharpHolderRecoveryAtFixedVolume : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ a b r : ℝ, 0 < a → a < r → r < b →
    ∀ γ : ℝ, 1 / (n : ℝ) < γ → ∀ δ C : ℝ, 0 < δ → 0 < C →
      ∃ E F : FullEllipsoid n,
        E.axesIn a b ∧ F.axesIn a b ∧
        (∀ i, |E.semiaxis i - r| < δ) ∧
        (∀ i, |F.semiaxis i - r| < δ) ∧ E.volume n = F.volume n ∧
        C * Real.rpow (E.volumeDistance F) γ < E.axisDistance F

/-- The n+1 real coefficients of the polynomial in the squared variable. -/
abbrev Coefficients (n : ℕ) := Fin (n + 1) → ℝ

/-- The even polynomial Q(t) with the specified coefficients. -/
def coefficientPolynomial {n : ℕ} (e : Coefficients n) (t : ℝ) : ℝ :=
  ∑ j : Fin (n + 1), e j * t ^ (2 * j.val)

/-- The part of Q with coefficient index below k. -/
def coefficientHead {n : ℕ} (e : Coefficients n) (k : ℕ) (t : ℝ) : ℝ :=
  ∑ j : Fin (n + 1), if j.val < k then e j * t ^ (2 * j.val) else 0

/-- Derivative of the even polynomial Q. -/
def coefficientDerivative {n : ℕ} (e : Coefficients n) (t : ℝ) : ℝ :=
  ∑ j : Fin (n + 1), (2 * j.val : ℝ) * e j * t ^ (2 * j.val - 1)

/-- Derivative of the truncated polynomial Q_k. -/
def coefficientHeadDerivative {n : ℕ} (e : Coefficients n) (k : ℕ) (t : ℝ) : ℝ :=
  ∑ j : Fin (n + 1), if j.val < k then
    (2 * j.val : ℝ) * e j * t ^ (2 * j.val - 1) else 0

/-- The coefficient integral in equation (3), with no real-rootedness restriction. -/
def coefficientTransform {n : ℕ} (e : Coefficients n) (k : ℕ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), (1 / 2 : ℝ) * Real.rpow t (-(k : ℝ)) *
    (coefficientHead e k t * coefficientDerivative e t -
      coefficientHeadDerivative e k t * coefficientPolynomial e t) *
    Real.rpow (coefficientPolynomial e t) (-(3 / 2 : ℝ))

/-- Mellin moment of Q to the power -3/2 on the positive real axis. -/
def mellinMoment {n : ℕ} (e : Coefficients n) (r : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), Real.rpow t (r - 1) *
    Real.rpow (coefficientPolynomial e t) (-(3 / 2 : ℝ))

/-- The internal coefficient index is within the literal free-coordinate range.
The two excluded endpoints are precisely the constant and leading coefficients. -/
theorem fixedEndpointIndexBound (m : ℕ) (j : Fin (m + 1 + 1))
    (h0 : ¬ j.val = 0) (hn : ¬ j.val = m + 1) : j.val - 1 < m := by
  omega

/-- The degree m+1 coefficient vector with the constant and leading coefficients fixed. -/
def fixedEndpoints (m : ℕ) (e0 en : ℝ) (x : Fin m → ℝ) : Coefficients (m + 1) :=
  fun j => if h0 : j.val = 0 then e0 else
    if hn : j.val = m + 1 then en else x ⟨j.val - 1, fixedEndpointIndexBound m j h0 hn⟩

/-- The m internal components of the coefficient integral transform. -/
def coefficientMap (m : ℕ) (e0 en : ℝ) (x : Fin m → ℝ) : Fin m → ℝ :=
  fun k => coefficientTransform (fixedEndpoints m e0 en x) (k.val + 1)

/-- Strict positivity of every principal determinant, including the empty determinant. -/
def principalJacobianPositive {m : ℕ} (J : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  ∀ s : Finset (Fin m), 0 < (J.submatrix (fun i : s => i.val) (fun i : s => i.val)).det

/-- The exact moment formula for the coefficient Jacobian. -/
def coefficientJacobian {n : ℕ} (e : Coefficients n)
    (k j : Fin (n - 1)) : ℝ :=
  let kk := k.val + 1
  let jj := j.val + 1
  (1 / 2 : ℝ) * if k ≤ j then
    ∑ l : Fin (n + 1), if l.val < kk then
      ((kk : ℝ) - l.val) * e l *
        mellinMoment e (2 * (jj : ℝ) - (kk : ℝ) + 2 * (l.val : ℝ)) else 0
  else
    ∑ l : Fin (n + 1), if kk < l.val then
      ((l.val : ℝ) - kk) * e l *
        mellinMoment e (2 * (jj : ℝ) - (kk : ℝ) + 2 * (l.val : ℝ)) else 0

/-- The matrix interpreted as the usual continuous linear map on a finite coordinate space. -/
def matrixDerivative {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  A.toLin'.toContinuousLinearMap

/-- The Jacobian after substituting the fixed endpoints. -/
def fixedCoefficientJacobian (m : ℕ) (e0 en : ℝ) (x : Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ := coefficientJacobian (fixedEndpoints m e0 en x)

/-- The closed nonnegative orthant of internal coefficients. -/
def closedCoefficientOrthant (m : ℕ) : Set (Fin m → ℝ) := {x | 0 ≤ x}

/-- The coefficient map with domain restricted to the closed orthant. -/
def restrictedCoefficientMap (m : ℕ) (e0 en : ℝ) : closedCoefficientOrthant m → (Fin m → ℝ) :=
  fun x => coefficientMap m e0 en x

/-- All clauses of Theorem 2.1: smooth neighborhood, principal minors, exact derivative, strict bounds, proper embedding and smooth ambient local inverses. -/
structure CoefficientTransformConclusion (m : ℕ) (e0 en : ℝ) : Prop where
  injective : Set.InjOn (coefficientMap m e0 en) (closedCoefficientOrthant m)
  smoothNeighborhood : ∃ U : Set (Fin m → ℝ), IsOpen U ∧ closedCoefficientOrthant m ⊆ U ∧
    ContDiffOn ℝ ∞ (coefficientMap m e0 en) U
  principalMinors : ∀ x, 0 ≤ x → principalJacobianPositive (fixedCoefficientJacobian m e0 en x)
  exactDerivative : ∀ x, 0 ≤ x → HasFDerivAt (coefficientMap m e0 en)
    (matrixDerivative (fixedCoefficientJacobian m e0 en x)) x
  strictBound : ∀ x, 0 ≤ x → ∀ i, Real.sqrt (x i) < coefficientMap m e0 en x i
  proper : IsProperMap (restrictedCoefficientMap m e0 en)
  embedding : Topology.IsClosedEmbedding (restrictedCoefficientMap m e0 en)
  closedImage : IsClosed (Set.range (restrictedCoefficientMap m e0 en))
  smoothLocalInverse : ∀ x, 0 ≤ x → ∃ G : (Fin m → ℝ) → (Fin m → ℝ),
    ContDiffAt ℝ ∞ G (coefficientMap m e0 en x) ∧
    (∀ᶠ y in 𝓝 x, G (coefficientMap m e0 en y) = y) ∧
    (∀ᶠ z in 𝓝 (coefficientMap m e0 en x), coefficientMap m e0 en (G z) = z)

/-- The product of 1+a_i squared times X, whose coefficients are elementary symmetric functions. -/
def axisCoefficientPolynomial {n : ℕ} (a : Fin n → ℝ) : ℝ[X] :=
  ∏ i, (1 + C (a i ^ 2) * X)

/-- Elementary symmetric functions of the squared semiaxes. -/
def axisCoefficients {n : ℕ} (a : Fin n → ℝ) : Coefficients n :=
  fun j => (axisCoefficientPolynomial a).coeff j.val


end EllipsoidVerification

open EllipsoidVerification
namespace PalomarEllipsoid

/-- The coefficient transform on Mathlib's standard quadrant, using its literal
Euclidean coordinate entries. No auxiliary coordinate transport is part of
this definition. -/
def coefficientQuadrantMap (m : ℕ) (e0 en : ℝ) :
    EuclideanQuadrant m → (Fin m → ℝ) :=
  fun x => coefficientMap m e0 en (fun i => x.val i)

/-- Theorem 1.1 of the accompanying paper, with all source hypotheses retained. -/
theorem intrinsic_reconstruction : IntrinsicReconstruction := by sorry

/-- Theorem 1.2, uniform estimate of the accompanying paper, with all source hypotheses retained. -/
theorem uniform_holder_recovery : UniformHolderRecovery := by sorry

/-- Theorem 1.2, sharpness of the accompanying paper, with all source hypotheses retained. -/
theorem sharp_holder_recovery : SharpHolderRecovery := by sorry

/-- Theorem 1.2, equal-volume sharpness of the accompanying paper, with all source hypotheses retained. -/
theorem sharp_holder_recovery_at_fixed_volume : SharpHolderRecoveryAtFixedVolume := by sorry

/-- Theorem 2.1 of the accompanying paper, with all source hypotheses retained. -/
theorem coefficient_transform_theorem {m : ℕ} {e0 en : ℝ}
    (h0 : 0 < e0) (hn : 0 < en) : CoefficientTransformConclusion m e0 en := by sorry

/-- Theorem 2.1, manifold with corners interpretation of the accompanying paper, with all source hypotheses retained. -/
theorem coefficient_transform_manifold_with_corners {m : ℕ} {e0 en : ℝ}
    (h0 : 0 < e0) (hn : 0 < en) :
    Manifold.IsSmoothEmbedding (𝓡c m) 𝓘(ℝ, Fin m → ℝ) ∞
      (coefficientQuadrantMap m e0 en) ∧
    IsProperMap (coefficientQuadrantMap m e0 en) ∧
    IsClosed (Set.range (coefficientQuadrantMap m e0 en)) := by sorry

/-- Section 5.1 of the accompanying paper, with all source hypotheses retained. -/
theorem measured_coefficient_box {n : ℕ} (hn : 0 < n) (E : FullEllipsoid n)
    (k : Fin (n + 1)) (hk : 0 < k.val) (hkn : k.val < n) :
    (n.choose k.val : ℝ) * (E.volume n / unitBallVolume n) ^ (2 * (k.val : ℝ) / n) ≤
      axisCoefficients E.semiaxis k ∧
    axisCoefficients E.semiaxis k < (E.volume k.val / unitBallVolume k.val) ^ 2 ∧
    axisCoefficients E.semiaxis (Fin.last n) = (E.volume n / unitBallVolume n) ^ 2 := by sorry

end PalomarEllipsoid

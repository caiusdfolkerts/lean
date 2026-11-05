module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Topology.Instances.RealVectorSpace

@[expose] public section

/-!
# Geometric quantities in the ellipsoid manuscript

Intrinsic volumes in this file are defined from the *actual Lebesgue volumes*
of parallel bodies. The polynomial is recovered by interpolation at the
nonnegative integers. Thus an integral formula for these quantities requires
a proof of the Steiner polynomial identity; it is not part of the definition.

An ellipsoid is represented by its centre, an orthogonal frame, and positive
semiaxes. Repeated semiaxes are allowed. This is the usual full-dimensional
ellipsoid parameterization, not a regular-spectrum restriction.
-/

noncomputable section

open MeasureTheory Set Polynomial
open scoped BigOperators Pointwise

namespace EllipsoidVerification

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

def unitBallVolume (n : ℕ) : ℝ :=
  (volume (Metric.closedBall (0 : Space n) 1)).toReal

def parallelBody {n : ℕ} (K : Set (Space n)) (r : ℝ) : Set (Space n) :=
  K + Metric.closedBall 0 r

def parallelVolume {n : ℕ} (K : Set (Space n)) (r : ℝ) : ℝ :=
  (volume (parallelBody K r)).toReal

def steinerInterpolant {n : ℕ} (K : Set (Space n)) : ℝ[X] :=
  Lagrange.interpolate Finset.univ (fun i : Fin (n + 1) => (i.val : ℝ))
    (fun i => parallelVolume K i.val)

def intrinsicVolume {n : ℕ} (K : Set (Space n)) (k : ℕ) : ℝ :=
  if k ≤ n then (steinerInterpolant K).coeff (n - k) / unitBallVolume (n - k) else 0

/-- The literal geometric correspondence that must be proved before using
the interpolated coefficients as the coefficients of every parallel body. -/
def HasSteinerFormula {n : ℕ} (K : Set (Space n)) : Prop :=
  ∀ r : ℝ, 0 ≤ r → parallelVolume K r = (steinerInterpolant K).eval r

def axisMap {n : ℕ} (a : Fin n → ℝ) (x : Space n) : Space n :=
  WithLp.toLp 2 (fun i => a i * x i)

structure FullEllipsoid (n : ℕ) where
  center : Space n
  frame : Space n ≃ₗᵢ[ℝ] Space n
  semiaxis : Fin n → ℝ
  semiaxis_pos : ∀ i, 0 < semiaxis i

namespace FullEllipsoid

def body {n : ℕ} (E : FullEllipsoid n) : Set (Space n) :=
  (fun x => E.center + E.frame (axisMap E.semiaxis x)) '' Metric.closedBall 0 1

def volume {n : ℕ} (E : FullEllipsoid n) (k : ℕ) : ℝ :=
  intrinsicVolume E.body k

def sphere (n : ℕ) (r : ℝ) (hr : 0 < r) : FullEllipsoid n where
  center := 0
  frame := LinearIsometryEquiv.refl ℝ (Space n)
  semiaxis := fun _ => r
  semiaxis_pos := fun _ => hr

def axesIn {n : ℕ} (E : FullEllipsoid n) (a b : ℝ) : Prop :=
  ∀ i, a ≤ E.semiaxis i ∧ E.semiaxis i ≤ b

def congruent {n : ℕ} (E F : FullEllipsoid n) : Prop :=
  ∃ T : Space n ≃ᵢ Space n, T '' E.body = F.body

def axisDistance {n : ℕ} (E F : FullEllipsoid n) : ℝ :=
  ⨅ σ : Equiv.Perm (Fin n), ⨆ i : Fin n, |E.semiaxis i - F.semiaxis (σ i)|

def volumeDistance {n : ℕ} (E F : FullEllipsoid n) : ℝ :=
  ⨆ k : Fin n, |E.volume (k.val + 1) - F.volume (k.val + 1)|

end FullEllipsoid

/-- Theorem 1.1, with literal sets and Euclidean congruence. -/
def IntrinsicReconstruction : Prop :=
  ∀ (n : ℕ) (E F : FullEllipsoid n),
    (∀ k : ℕ, 1 ≤ k → k ≤ n → E.volume k = F.volume k) → E.congruent F

/-- The quantitative estimate of Theorem 1.2. The positive dimension
condition gives the intended meaning of the exponent `1 / n`. -/
def UniformHolderRecovery : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ a b : ℝ, 0 < a → a ≤ b →
    ∃ C : ℝ, 0 < C ∧ ∀ E F : FullEllipsoid n,
      E.axesIn a b → F.axesIn a b →
      E.axisDistance F ≤ C * Real.rpow (E.volumeDistance F) (1 / (n : ℝ))

/-- No exponent larger than `1/n` works in any semiaxis neighborhood of
a sphere. The inequality is explicitly violated for every proposed constant. -/
def SharpHolderRecovery : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ a b r : ℝ, 0 < a → a < r → r < b →
    ∀ γ : ℝ, 1 / (n : ℝ) < γ → ∀ δ C : ℝ, 0 < δ → 0 < C →
      ∃ E F : FullEllipsoid n,
        E.axesIn a b ∧ F.axesIn a b ∧
        (∀ i, |E.semiaxis i - r| < δ) ∧
        (∀ i, |F.semiaxis i - r| < δ) ∧
        C * Real.rpow (E.volumeDistance F) γ < E.axisDistance F

/-- The additional equal-volume sharpness clause of Theorem 1.2. -/
def SharpHolderRecoveryAtFixedVolume : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ a b r : ℝ, 0 < a → a < r → r < b →
    ∀ γ : ℝ, 1 / (n : ℝ) < γ → ∀ δ C : ℝ, 0 < δ → 0 < C →
      ∃ E F : FullEllipsoid n,
        E.axesIn a b ∧ F.axesIn a b ∧
        (∀ i, |E.semiaxis i - r| < δ) ∧
        (∀ i, |F.semiaxis i - r| < δ) ∧ E.volume n = F.volume n ∧
        C * Real.rpow (E.volumeDistance F) γ < E.axisDistance F

theorem steinerInterpolant_eval_node {n : ℕ} (K : Set (Space n)) (i : Fin (n + 1)) :
    (steinerInterpolant K).eval (i.val : ℝ) = parallelVolume K i.val := by
  classical
  unfold steinerInterpolant
  apply Lagrange.eval_interpolate_at_node
    (v := fun j : Fin (n + 1) => (j.val : ℝ))
    (fun j : Fin (n + 1) => parallelVolume K j.val)
  · intro i hi j hj h
    exact Fin.ext (Nat.cast_injective h)
  · exact Finset.mem_univ i

@[fun_prop] theorem continuous_axisMap {n : ℕ} (a : Fin n → ℝ) :
    Continuous (axisMap a) := by
  apply (PiLp.continuous_toLp 2 _).comp
  exact continuous_pi fun i => continuous_const.mul (PiLp.continuous_apply 2 _ i)

theorem FullEllipsoid.isCompact_body {n : ℕ} (E : FullEllipsoid n) :
    IsCompact E.body := by
  apply (isCompact_closedBall (0 : Space n) 1).image
  exact continuous_const.add (E.frame.continuous.comp (continuous_axisMap E.semiaxis))

theorem FullEllipsoid.nonempty_body {n : ℕ} (E : FullEllipsoid n) :
    E.body.Nonempty := by
  exact Set.Nonempty.image _ ⟨0, by simp⟩

end EllipsoidVerification

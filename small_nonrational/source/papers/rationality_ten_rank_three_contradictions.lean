module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Explicit real obstructions in the seven- and eight-point cores

These are the determinant contradictions after projective frame
normalization. The universal geometric normalizations and the finite
classification are supplied separately; these statements do not assume
that a generic configuration already lies in one of the charts.

DRAFT: prepared during an unavailable execution environment; not compiled.
-/

namespace Papers.RationalityTen.RankThreeContradictions

def determinant (a b c : Fin 3 → ℝ) : ℝ := (Matrix.of ![a, b, c]).det

/-- The Fano core with root lines 012,034,056 and remaining lines
135,146,236,245. The frame is 0=e₀,1=e₁,3=e₂,6=(1,1,1).
The other three points have coordinates 2=(u,1,0),4=(v,0,1),
5=(0,w,1). -/
theorem fano_normalized_impossible (u v w : ℝ)
    (h146 : determinant ![0,1,0] ![v,0,1] ![1,1,1] = 0)
    (h236 : determinant ![u,1,0] ![0,0,1] ![1,1,1] = 0)
    (h056 : determinant ![1,0,0] ![0,w,1] ![1,1,1] = 0)
    (h245 : determinant ![u,1,0] ![v,0,1] ![0,w,1] = 0) : False := by
  norm_num [determinant, Matrix.det_fin_three] at h146 h236 h056 h245
  have hu : u = 1 := by linarith
  have hv : v = 1 := by linarith
  have hw : w = 1 := by linarith
  subst u
  subst v
  subst w
  norm_num at h245

/-- The last four incidences in the paper's MacLane pattern, in zero-based
labels. The four initial lines give 4=(a,0,1),5=(1,b,1),
6=(c,1,1),7=(0,d,1). The first two equations below identify c=a and d=b;
the last two then force ab=1=a+b. -/
theorem maclane_normalized_impossible (a b c d : ℝ)
    (h057 : determinant ![1,0,0] ![1,b,1] ![0,d,1] = 0)
    (h146 : determinant ![0,1,0] ![a,0,1] ![c,1,1] = 0)
    (h256 : determinant ![0,0,1] ![1,b,1] ![c,1,1] = 0)
    (h347 : determinant ![1,1,1] ![a,0,1] ![0,d,1] = 0) : False := by
  norm_num [determinant, Matrix.det_fin_three] at h057 h146 h256 h347
  have hc : c = a := by linarith
  have hd : d = b := by linarith
  subst c
  subst d
  nlinarith [sq_nonneg (a - b)]

/-- The scalar obstruction itself: it excludes singular or zero parameter
values as well, without a denominator or sign assumption. -/
theorem no_real_maclane_parameters (u v : ℝ) (hprod : u * v = 1)
    (hsum : u + v = 1) : False := by
  nlinarith [sq_nonneg (u - v)]

end Papers.RationalityTen.RankThreeContradictions

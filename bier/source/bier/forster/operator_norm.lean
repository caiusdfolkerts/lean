import bier.forster.bound
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Forster's inequality with the usual Euclidean operator norm -/

noncomputable section

namespace Bier.Forster

open Classical Finset Matrix WithLp

variable {R C : Type*} [Fintype R] [Fintype C]

/-- The spectral norm: the operator norm between the standard Euclidean spaces. -/
def spectralNorm (H : Matrix R C ℝ) : ℝ :=
  ‖H.toEuclideanLin.toContinuousLinearMap‖

theorem spectralNorm_nonneg (H : Matrix R C ℝ) : 0 ≤ spectralNorm H := norm_nonneg _

theorem spectralNorm_transpose (H : Matrix R C ℝ) : spectralNorm Hᵀ = spectralNorm H := by
  have he : Hᵀ.toEuclideanLin = H.toEuclideanLin.adjoint := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.toEuclideanLin_conjTranspose_eq_adjoint H
  unfold spectralNorm
  rw [he, LinearMap.adjoint_toContinuousLinearMap]
  exact ContinuousLinearMap.adjoint.norm_map _

theorem squaredOperatorBound_spectralNorm (H : Matrix R C ℝ) :
    SquaredOperatorBound H (spectralNorm H ^ 2) := by
  intro x
  let T := Hᵀ.toEuclideanLin.toContinuousLinearMap
  let y : EuclideanSpace ℝ R := toLp 2 x
  have hb : ‖T y‖ ^ 2 ≤ (‖T‖ * ‖y‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
      (T.le_opNorm y)
  have he : (T y : EuclideanSpace ℝ C) = toLp 2 (Hᵀ *ᵥ x) := rfl
  rw [he, mul_pow, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq] at hb
  have hn : ‖T‖ = spectralNorm H := spectralNorm_transpose H
  simpa only [hn, y, PiLp.toLp_apply, Matrix.mulVec, Matrix.transpose_apply, dotProduct] using hb

/-- Forster's spectral sign-rank inequality for each realizing matrix. -/
theorem forster_spectral (H M : Matrix R C ℝ)
    (hH : Bier.IsSignMatrix H) (hM : Bier.SignRealizes H M) :
    Real.sqrt ((Fintype.card R : ℝ) * Fintype.card C) ≤ (M.rank : ℝ) * spectralNorm H := by
  have hh := forster_bound H M hH hM (spectralNorm H ^ 2) (sq_nonneg _)
    (squaredOperatorBound_spectralNorm H)
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg (by positivity) (spectralNorm_nonneg H), ?_⟩
  simpa only [mul_pow, mul_comm] using hh

/-- The usual lower bound on sign rank, without any nondegeneracy or general
position hypothesis on a realizing matrix. -/
theorem signRank_spectral (H : Matrix R C ℝ) (hH : Bier.IsSignMatrix H) :
    Real.sqrt ((Fintype.card R : ℝ) * Fintype.card C) ≤
      (Bier.signRank H : ℝ) * spectralNorm H := by
  obtain ⟨M, hM, hr⟩ := Bier.exists_rank_eq_signRank hH
  simpa only [hr] using forster_spectral H M hH hM

end Bier.Forster

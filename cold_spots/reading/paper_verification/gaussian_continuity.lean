module
public import PaperVerification.GaussianFourier
public import PaperVerification.GaussianIdentities
public import Mathlib.Analysis.Normed.Group.FunctionSeries
@[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

theorem continuous_fourierGaussian {β : ℝ} (hβ : 0 < β) :
    Continuous (fourierGaussian β) := by
  unfold fourierGaussian
  apply continuous_tsum
    (u := fun n : ℤ ↦ Real.exp (-β * (n : ℝ) ^ 2))
  · intro n
    exact continuous_const.mul (Real.continuous_cos.comp
      ((continuous_const.mul continuous_id).mul continuous_const))
  · exact summable_gaussian_zero hβ
  · intro n t
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)

theorem continuous_gaussian {α : ℝ} (hα : 0 < α) : Continuous (gaussian α) := by
  have hfun : gaussian α = fun t ↦
      Real.sqrt (Real.pi / α) * fourierGaussian (Real.pi ^ 2 / α) t :=
    funext (gaussian_poisson hα)
  rw [hfun]
  exact continuous_const.mul
    (continuous_fourierGaussian (div_pos (sq_pos_of_pos Real.pi_pos) hα))

theorem continuous_alternatingGaussian {α : ℝ} (hα : 0 < α) :
    Continuous (alternatingGaussian α) := by
  have hfun : alternatingGaussian α = fun t ↦
      gaussian (4 * α) (t / 2) - gaussian (4 * α) ((t - 1) / 2) :=
    funext (alternatingGaussian_split hα)
  rw [hfun]
  have h4 := continuous_gaussian (show 0 < 4 * α by positivity)
  exact (h4.comp (continuous_id.div_const 2)).sub
    (h4.comp ((continuous_id.sub continuous_const).div_const 2))

end PaperVerification.ColdSpots

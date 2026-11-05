module
public import PaperVerification.ThetaRelations
public import PaperVerification.GaussianAlternating
public import Mathlib.Analysis.SpecialFunctions.Arsinh
@[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

def thetaR (α : ℝ) : ℝ :=
  Real.arsinh (alternatingGaussian α 0 ^ 2 / gaussian α (1 / 2) ^ 2)

def thetaP (α t : ℝ) : ℝ :=
  Real.arsinh (alternatingGaussian α t ^ 2 / Real.sqrt (thetaScale α t))

lemma cosh_arsinh_of_hyperbola {x y : ℝ} (hx : 0 ≤ x) (hxy : x ^ 2 - y ^ 2 = 1) :
    Real.cosh (Real.arsinh y) = x := by
  rw [Real.cosh_arsinh]
  exact (Real.sqrt_eq_iff_eq_sq (by positivity) hx).mpr (by linarith)

theorem thetaR_pos {α : ℝ} (hα : 0 < α) : 0 < thetaR α := by
  apply Real.arsinh_pos_iff.mpr
  exact div_pos (sq_pos_of_pos (alternatingGaussian_zero_pos hα))
    (sq_pos_of_pos (gaussian_pos hα (1 / 2)))

theorem thetaR_sinh (α : ℝ) :
    Real.sinh (thetaR α) = alternatingGaussian α 0 ^ 2 / gaussian α (1 / 2) ^ 2 := by
  exact Real.sinh_arsinh _

theorem thetaR_cosh {α : ℝ} (hα : 0 < α) :
    Real.cosh (thetaR α) = gaussian α 0 ^ 2 / gaussian α (1 / 2) ^ 2 := by
  apply cosh_arsinh_of_hyperbola (by positivity)
  have hq := gaussian_constant_quartic hα
  have hc : gaussian α (1 / 2) ≠ 0 := (gaussian_pos hα (1 / 2)).ne'
  field_simp [hc]
  nlinarith [hq]

theorem thetaP_sinh (α t : ℝ) :
    Real.sinh (thetaP α t) = alternatingGaussian α t ^ 2 / Real.sqrt (thetaScale α t) := by
  exact Real.sinh_arsinh _

theorem thetaP_cosh {α : ℝ} (hα : 0 < α) (t : ℝ) :
    Real.cosh (thetaP α t) = gaussian α t ^ 2 / Real.sqrt (thetaScale α t) := by
  apply cosh_arsinh_of_hyperbola (by positivity)
  have hs := thetaScale_pos hα t
  have hroot := Real.sq_sqrt hs.le
  have hr : Real.sqrt (thetaScale α t) ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  field_simp [hr]
  change Real.sqrt (thetaScale α t) ^ 2 = gaussian α t ^ 4 - alternatingGaussian α t ^ 4 at hroot
  nlinarith [hroot]

theorem thetaP_cosh_sub {α : ℝ} (hα : 0 < α) (t : ℝ) :
    Real.cosh (thetaR α - thetaP α t) =
      gaussian α (t - 1 / 2) ^ 2 / Real.sqrt (thetaScale α t) := by
  rw [Real.cosh_sub, thetaR_cosh hα, thetaP_cosh hα, thetaR_sinh, thetaP_sinh]
  have hc : gaussian α (1 / 2) ≠ 0 := (gaussian_pos hα (1 / 2)).ne'
  have hr : Real.sqrt (thetaScale α t) ≠ 0 := (Real.sqrt_pos.mpr (thetaScale_pos hα t)).ne'
  field_simp [hc, hr]
  rw [show (2 * t - 1) / 2 = t - 1 / 2 by ring]
  nlinarith [(gaussian_quadratic_relations hα t).1]

theorem thetaP_sinh_sub {α : ℝ} (hα : 0 < α) (t : ℝ) :
    Real.sinh (thetaR α - thetaP α t) =
      alternatingGaussian α (t - 1 / 2) ^ 2 / Real.sqrt (thetaScale α t) := by
  rw [Real.sinh_sub, thetaR_cosh hα, thetaP_cosh hα, thetaR_sinh, thetaP_sinh]
  have hc : gaussian α (1 / 2) ≠ 0 := (gaussian_pos hα (1 / 2)).ne'
  have hr : Real.sqrt (thetaScale α t) ≠ 0 := (Real.sqrt_pos.mpr (thetaScale_pos hα t)).ne'
  field_simp [hc, hr]
  rw [show (2 * t - 1) / 2 = t - 1 / 2 by ring]
  nlinarith [gaussian_quadratic_relation_reverse hα t]

/-- The hyperbolic parameter lies in the full claimed range; no monotonicity assumption is used. -/
theorem thetaP_mem_Icc {α : ℝ} (hα : 0 < α) (t : ℝ) :
    thetaP α t ∈ Set.Icc 0 (thetaR α) := by
  constructor
  · exact Real.arsinh_nonneg_iff.mpr (div_nonneg (sq_nonneg _) (Real.sqrt_nonneg _))
  · have h := Real.sinh_nonneg_iff.mp (show 0 ≤ Real.sinh (thetaR α - thetaP α t) by
      rw [thetaP_sinh_sub hα]
      positivity)
    linarith

theorem continuous_thetaScale {α : ℝ} (hα : 0 < α) : Continuous (thetaScale α) :=
  ((continuous_gaussian hα).pow 4).sub ((continuous_alternatingGaussian hα).pow 4)

theorem continuous_thetaP {α : ℝ} (hα : 0 < α) : Continuous (thetaP α) := by
  apply Real.continuous_arsinh.comp
  exact ((continuous_alternatingGaussian hα).pow 2).div
    (Real.continuous_sqrt.comp (continuous_thetaScale hα))
    (fun t ↦ (Real.sqrt_pos.mpr (thetaScale_pos hα t)).ne')

theorem thetaP_zero {α : ℝ} (hα : 0 < α) : thetaP α 0 = thetaR α := by
  apply Real.sinh_injective
  rw [thetaP_sinh, thetaR_sinh]
  have hs : thetaScale α 0 = gaussian α (1 / 2) ^ 4 := by
    unfold thetaScale
    nlinarith [gaussian_constant_quartic hα]
  rw [hs, show gaussian α (1 / 2) ^ 4 = (gaussian α (1 / 2) ^ 2) ^ 2 by ring,
    Real.sqrt_sq (sq_nonneg _)]

theorem thetaP_half (α : ℝ) : thetaP α (1 / 2) = 0 := by
  apply Real.sinh_injective
  rw [thetaP_sinh, alternatingGaussian_half]
  simp

theorem thetaP_quarter {α : ℝ} (hα : 0 < α) : thetaP α (1 / 4) = thetaR α / 2 := by
  have hD : alternatingGaussian α ((1 / 4 : ℝ) - 1 / 2) = alternatingGaussian α (1 / 4) := by
    rw [show (1 / 4 : ℝ) - 1 / 2 = -(1 / 4 : ℝ) by ring, alternatingGaussian_even]
  have hs := thetaP_sinh_sub hα (1 / 4)
  rw [hD, ← thetaP_sinh] at hs
  have he := Real.sinh_injective hs
  linarith

/-- The measurable parameter map used for the pushforward in Proposition 3.2. -/
def thetaArcPoint {α : ℝ} (hα : 0 < α) (t : Set.Icc (0 : ℝ) (1 / 2)) :
    Set.Icc (0 : ℝ) (thetaR α) :=
  ⟨thetaP α t, thetaP_mem_Icc hα t⟩

theorem continuous_thetaArcPoint {α : ℝ} (hα : 0 < α) : Continuous (thetaArcPoint hα) :=
  ((continuous_thetaP hα).comp continuous_subtype_val).subtype_mk _

end PaperVerification.ColdSpots

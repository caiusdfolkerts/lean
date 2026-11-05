module

public import PaperVerification.ToricStarStrictSupport
public import Mathlib.Algebra.Order.Archimedean.Basic

@[expose] public section

/-!
# Integral strict support survives smooth star subdivisions

The all-small perturbation theorem permits ε=1/N. Multiplication by N makes
all coefficients integral: the exceptional coefficient is N times the old
focus sum minus one, and every other coefficient is N times its old value.
This provides the integral descending cost required by primitive reductions,
without assuming the primitive nef criterion or a rational approximation.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem exists_integral_strictSupport_starSubdivision
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun v => (H v : ℝ)))
    (t : Finset (Lattice n)) (ht : t ∈ «Σ».cones) (hne : t.Nonempty)
    (hcard : 2 ≤ t.card) :
    ∃ K : Lattice n → ℤ,
      («Σ».starSubdivision t ht hne).IsStrictSupport (fun v => (K v : ℝ)) := by
  obtain ⟨δ, hδ, hsmall⟩ :=
    «Σ».strictSupport_starSubdivision_all_small (fun v => (H v : ℝ)) hH t ht hne hcard
  obtain ⟨N, hNlarge⟩ := exists_nat_gt (max (1 : ℝ) δ⁻¹)
  have hNR : (0 : ℝ) < N := lt_trans zero_lt_one ((le_max_left _ _).trans_lt hNlarge)
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNR
  have hε : (0 : ℝ) < (N : ℝ)⁻¹ := inv_pos.mpr hNR
  have hεle : (N : ℝ)⁻¹ ≤ δ := by
    have hlarge : δ⁻¹ < (N : ℝ) := (le_max_right _ _).trans_lt hNlarge
    have hmul := mul_lt_mul_of_pos_left hlarge hδ
    rw [mul_inv_cancel₀ (ne_of_gt hδ)] at hmul
    rw [← one_div]
    apply (div_le_iff₀ hNR).mpr
    nlinarith
  have hs := hsmall (N : ℝ)⁻¹ hε hεle
  have hscaled := IsStrictSupport.smul («Σ».starSubdivision t ht hne) hs hNR
  let K : Lattice n → ℤ := fun v =>
    if v = ∑ w ∈ t, w then (N : ℤ) * (∑ w ∈ t, H w) - 1 else (N : ℤ) * H v
  have hcoeff : (fun v => (K v : ℝ)) = (N : ℝ) •
      (fun v => starCoefficientBase (fun w => (H w : ℝ)) t v +
        (N : ℝ)⁻¹ * starCoefficientSlope t v) := by
    funext v
    by_cases hv : v = ∑ w ∈ t, w
    · simp only [K, starCoefficientBase, starCoefficientSlope, if_pos hv,
        Pi.smul_apply, smul_eq_mul, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
        Int.cast_sum, Int.cast_one]
      field_simp
      ring
    · simp only [K, starCoefficientBase, starCoefficientSlope, if_neg hv,
        Pi.smul_apply, smul_eq_mul, mul_zero, add_zero, Int.cast_mul, Int.cast_natCast]
  exact ⟨K, hcoeff.symm ▸ hscaled⟩

end SmoothCompleteFan

end PaperVerification.ToricGeometry

module

public import VolumePolynomials.HolonomySeries
public import VolumePolynomials.HolonomyAngle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

@[expose] public section
noncomputable section

namespace VolumePolynomials.Holonomy

open Polynomial.Chebyshev

theorem orbit_snd_recurrence (n : ℕ) :
    (orbit (n + 2)).2 = (2 / 3 : ℝ) * (orbit (n + 1)).2 - (orbit n).2 := by
  first
  | rw [show n + 2 = (n + 1) + 1 by omega, orbit_succ, orbit_succ]
    dsimp [returnMap]
    ring

/-- Cayley–Hamilton in explicit coordinates, matched with the proved Chebyshev recurrence. -/
theorem orbit_snd_eq_chebyshev (n : ℕ) :
    (orbit (n + 1)).2 = -(U ℝ (n : ℤ)).eval (1 / 3) := by
  first
  | induction n using Nat.twoStepInduction with
    | zero => norm_num [orbit, returnMap]
    | one => norm_num [orbit, returnMap]
    | more n hn hn1 =>
        have hr := orbit_snd_recurrence (n + 1)
        rw [hn1, hn] at hr
        rw [show n + 2 + 1 = n + 1 + 2 by omega, hr]
        push_cast
        rw [U_add_two]
        simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
          Polynomial.eval_X]
        ring

theorem orbit_snd_mul_sin (n : ℕ) :
    -(orbit n).2 * Real.sin angle = Real.sin ((n : ℝ) * angle) := by
  first
  | cases n with
    | zero => simp
    | succ n =>
        rw [orbit_snd_eq_chebyshev, neg_neg]
        simpa only [cos_angle, Int.cast_natCast, Int.cast_add, Int.cast_one,
          Nat.cast_add, Nat.cast_one] using U_real_cos angle (n : ℤ)

theorem abs_orbit_snd (n : ℕ) :
    |(orbit n).2| = |Real.sin ((n : ℝ) * angle)| / Real.sin angle := by
  first
  | apply (eq_div_iff sin_angle_pos.ne').mpr
    have h := congrArg abs (orbit_snd_mul_sin n)
    simpa only [abs_mul, abs_neg, abs_of_pos sin_angle_pos] using h

theorem abs_det_orbit_gap (i k : ℕ) :
    |det (orbit i) (orbit (i + k))| =
      |Real.sin ((k : ℝ) * angle)| / Real.sin angle := by
  first
  | rw [det_orbit_add, abs_orbit_snd]

/-- The area contribution of a pair depends on its gap and a geometric factor. -/
theorem abs_det_weighted_gap (lam : ℝ) (hlam : 0 ≤ lam) (i k : ℕ) :
    |det (weightedOrbit lam i) (weightedOrbit lam (i + (k + 1)))| =
      (lam ^ 2) ^ i *
        (|Real.sin (((k + 1 : ℕ) : ℝ) * angle)| * lam ^ (k + 1) / Real.sin angle) := by
  first
  | rw [weightedOrbit, weightedOrbit, det_smul, abs_mul,
      abs_of_nonneg (mul_nonneg (pow_nonneg hlam i) (pow_nonneg hlam _)),
      abs_det_orbit_gap]
    rw [pow_two, mul_pow, pow_add]
    ring

end VolumePolynomials.Holonomy

module
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Ring.Basic
@[expose] public section
set_option autoImplicit false

/-!
# The pairing consequence of equality in Alexandrov–Fenchel

The first result is an elementary one-sided derivative argument for a
quadratic polynomial, proved using an explicit positive test value.  The
second applies it to a symmetric Minkowski-bilinear pairing.  No assertion
about support functions, area measures, or equality rigidity is assumed.
-/
namespace VolumeVerification.AFPairingEquality

theorem linear_coefficient_nonnegative (u v : ℝ)
    (h : ∀ s : ℝ, 0 ≤ s → 0 ≤ u * s + v * s ^ 2) : 0 ≤ u := by
  by_contra hu
  have hu' : u < 0 := lt_of_not_ge hu
  have hd : 0 < |v| + 1 := add_pos_of_nonneg_of_pos (abs_nonneg v) zero_lt_one
  let s : ℝ := -u / (|v| + 1)
  have hs : 0 < s := div_pos (neg_pos.mpr hu') hd
  have he : s * (|v| + 1) = -u := div_mul_cancel₀ _ hd.ne'
  have he' := congrArg (fun x : ℝ => x * s) he
  have hv : v * s ^ 2 ≤ |v| * s ^ 2 :=
    mul_le_mul_of_nonneg_right (le_abs_self v) (sq_nonneg s)
  have hpoly := h s hs.le
  nlinarith [sq_pos_of_pos hs]

/-- A real affine function nonnegative on the whole positive half-line has
nonnegative slope. This is used with an actual AF discriminant. -/
theorem affine_coefficient_nonnegative (c u : ℝ)
    (h : ∀ s : ℝ, 0 ≤ s → 0 ≤ c + u * s) : 0 ≤ u := by
  apply linear_coefficient_nonnegative u c
  intro t ht
  by_cases ht0 : t = 0
  · simp [ht0]
  have hp := mul_nonneg (h t⁻¹ (inv_nonneg.mpr ht)) (sq_nonneg t)
  have he : (c + u * t⁻¹) * t ^ 2 = u * t + c * t ^ 2 := by
    calc
      _ = c * t ^ 2 + u * (t⁻¹ * t) * t := by ring
      _ = _ := by rw [inv_mul_cancel₀ ht0]; ring
  rwa [he] at hp

/-- The scalar step for convex-hull rigidity. If two bodies have equal
pairings against a positive reference, and their difference is null, AF
applied after unequal positive additions of that reference fixes their
remaining pairing. The displayed inequality is exactly that expansion. -/
theorem pairing_le_of_shifted_AF (a b m k : ℝ) (hk : 0 < k)
    (haf : ∀ s : ℝ, 0 ≤ s →
      ((2 * b - a) + 2 * s * m + s ^ 2 * k) *
          (a + 2 * (s + 1) * m + (s + 1) ^ 2 * k) ≤
        (b + (2 * s + 1) * m + s * (s + 1) * k) ^ 2) : b ≤ a := by
  have hslope := affine_coefficient_nonnegative
    ((b - a - m) ^ 2 - a * k - 2 * k * (b - a)) (-2 * k * (b - a))
    (fun s hs => by
      have he :
          ((b - a - m) ^ 2 - a * k - 2 * k * (b - a)) +
              (-2 * k * (b - a)) * s =
            (b + (2 * s + 1) * m + s * (s + 1) * k) ^ 2 -
              (((2 * b - a) + 2 * s * m + s ^ 2 * k) *
                (a + 2 * (s + 1) * m + (s + 1) ^ 2 * k)) := by ring
      rw [he]
      exact sub_nonneg.mpr (haf s hs))
  have hm : k * (b - a) ≤ 0 := by linarith
  exact sub_nonpos.mp (nonpos_of_mul_nonpos_right hm hk)

theorem pairing_le_of_quadratic_inequalities (a b c d : ℝ) (ha : 0 < a)
    (h : ∀ s : ℝ, 0 ≤ s →
      a * (a + 2 * s * b + s ^ 2 * d) ≤ (a + s * c) ^ 2) : b ≤ c := by
  have hc := linear_coefficient_nonnegative (2 * a * (c - b)) (c ^ 2 - a * d)
    (fun s hs => by
      have he : (2 * a * (c - b)) * s + (c ^ 2 - a * d) * s ^ 2 =
          (a + s * c) ^ 2 - a * (a + 2 * s * b + s ^ 2 * d) := by ring
      rw [he]
      exact sub_nonneg.mpr (h s hs))
  have htwo : 0 < 2 * a := mul_pos zero_lt_two ha
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left htwo).mp hc)

/-- Equality at a positive self-pairing forces equality against every test
object.  The assumptions are the usual symmetry, additivity, nonnegative
homogeneity, and Alexandrov–Fenchel inequality of the pairing itself. -/
theorem equality_of_equal_positive_pairings
    {C : Type*} [Add C] [SMul ℝ C]
    (q : C → C → ℝ)
    (hsymm : ∀ A B, q A B = q B A)
    (hadd : ∀ A B T, q (A + B) T = q A T + q B T)
    (hsmul : ∀ (r : ℝ), 0 ≤ r → ∀ A T, q (r • A) T = r * q A T)
    (haf : ∀ A B, q A A * q B B ≤ q A B ^ 2)
    (A B : C) (a : ℝ) (ha : 0 < a)
    (hAA : q A A = a) (hAB : q A B = a) (hBB : q B B = a) :
    ∀ T, q A T = q B T := by
  have hadd_right (X Y Z : C) : q X (Y + Z) = q X Y + q X Z := by
    rw [hsymm X (Y + Z), hadd Y Z X, hsymm Y X, hsymm Z X]
  have hsmul_right (r : ℝ) (hr : 0 ≤ r) (X Y : C) :
      q X (r • Y) = r * q X Y := by
    rw [hsymm X (r • Y), hsmul r hr Y X, hsymm Y X]
  have step (X Y : C) (hXX : q X X = a) (hXY : q X Y = a)
      (hYY : q Y Y = a) (T : C) : q X T ≤ q Y T := by
    apply pairing_le_of_quadratic_inequalities a (q X T) (q Y T) (q T T) ha
    intro s hs
    have hself : q (X + s • T) (X + s • T) =
        a + 2 * s * q X T + s ^ 2 * q T T := by
      rw [hadd, hadd_right, hadd_right, hsmul s hs, hsmul s hs,
        hsmul_right s hs, hsmul_right s hs, hXX, hsymm T X]
      ring
    have hcross : q (X + s • T) Y = a + s * q Y T := by
      rw [hadd, hsmul s hs, hXY, hsymm T Y]
    have h := haf (X + s • T) Y
    rw [hself, hcross, hYY] at h
    simpa only [mul_comm] using h
  intro T
  exact le_antisymm (step A B hAA hAB hBB T)
    (step B A hBB ((hsymm B A).trans hAB) hAA T)

/-- Algebraic amplification from a weak equality to equality for the convex
hull. The only additional input about the hull `D` is its proved quadratic
valuation identity and monotonicity. The geometric application supplies both
from actual convex bodies. -/
theorem hull_pairings_of_weak_equality
    {C : Type*} [Add C] [SMul ℝ C]
    (q : C → C → ℝ)
    (hsymm : ∀ A B, q A B = q B A)
    (hadd : ∀ A B T, q (A + B) T = q A T + q B T)
    (hsmul : ∀ (r : ℝ), 0 ≤ r → ∀ A T, q (r • A) T = r * q A T)
    (haf : ∀ A B, q A A * q B B ≤ q A B ^ 2)
    (A B D H : C) (a : ℝ) (ha : 0 < a)
    (hAA : q A A = a) (hAB : q A B = a) (hBB : q B B = a)
    (hval : q D D + q A B = q D A + q D B)
    (hmono : a ≤ q D A) (hHH : 0 < q H H)
    (hweak : q D H = q A H) : ∀ T, q D T = q A T := by
  have hadd_right (X Y Z : C) : q X (Y + Z) = q X Y + q X Z := by
    rw [hsymm X (Y + Z), hadd Y Z X, hsymm Y X, hsymm Z X]
  have hsmul_right (r : ℝ) (hr : 0 ≤ r) (X Y : C) :
      q X (r • Y) = r * q X Y := by
    rw [hsymm X (r • Y), hsmul r hr Y X, hsymm Y X]
  have hexpand (X Y Z W : C) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
      q (X + s • Z) (Y + t • W) =
        q X Y + t * q X W + s * q Z Y + s * t * q Z W := by
    rw [hadd, hadd_right, hadd_right, hsmul s hs, hsmul s hs,
      hsmul_right t ht, hsmul_right t ht]
    ring
  have hABall := equality_of_equal_positive_pairings q hsymm hadd hsmul haf
    A B a ha hAA hAB hBB
  have hDB : q D B = q D A := by
    rw [hsymm D B, ← hABall D, hsymm A D]
  have hDD : q D D = 2 * q D A - a := by
    rw [hAB, hDB] at hval
    linarith
  have hDAle : q D A ≤ a := by
    apply pairing_le_of_shifted_AF a (q D A) (q A H) (q H H) hHH
    intro s hs
    have hs1 : 0 ≤ s + 1 := by linarith
    have h := haf (D + s • H) (A + (s + 1) • H)
    rw [hexpand D D H H s s hs hs,
      hexpand A A H H (s + 1) (s + 1) hs1 hs1,
      hexpand D A H H s (s + 1) hs hs1] at h
    rw [hsymm H D, hsymm H A, hDD, hAA, hweak] at h
    convert h using 1 <;> ring
  have hDA : q D A = a := le_antisymm hDAle hmono
  have hDD' : q D D = a := by rw [hDD, hDA]; ring
  exact equality_of_equal_positive_pairings q hsymm hadd hsmul haf
    D A a ha hDD' hDA hAA

end VolumeVerification.AFPairingEquality

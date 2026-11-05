module
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section
set_option autoImplicit false
noncomputable section

/-!
# The algebraic part of the Alexandrov–Fenchel argument

This proves the reverse Cauchy–Schwarz implication for a symmetric bilinear form
from negativity on one orthogonal hyperplane. It is only an algebraic dependency:
the mixed-volume form must still be constructed and its hyperplane inequality
proved geometrically before applying this to the binary realization theorem.

The reduction is the quadratic-form step used in Shenfeld–van Handel,
*Mixed volumes and the Bochner method*, Lemma 2.9. The proof below is direct
bilinear algebra and does not assume a spectral theorem or a geometric inequality.
-/

namespace VolumePolynomials

open LinearMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Negativity on one orthogonal hyperplane implies negativity on the
orthogonal hyperplane of any vector with positive quadratic value. -/
theorem bilinear_nonpos_on_positive_orthogonal
    (B : LinearMap.BilinForm ℝ E) (hB : ∀ x y, B x y = B y x) (e : E)
    (he : ∀ x, B x e = 0 → B x x ≤ 0)
    {y : E} (hy : 0 < B y y) {x : E} (hxy : B x y = 0) : B x x ≤ 0 := by
  first
  | by_contra hx
    have hxpos : 0 < B x x := lt_of_not_ge hx
    let z : E := B y e • x - B x e • y
    have hze : B z e = 0 := by
      simp only [z, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left]
      ring
    have hzz := he z hze
    have hyx : B y x = 0 := (hB y x).trans hxy
    have hzexp : B z z = (B y e) ^ 2 * B x x + (B x e) ^ 2 * B y y := by
      simp only [z, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right,
        LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hxy, hyx]
      ring
    rw [hzexp] at hzz
    have hterm : 0 ≤ (B x e) ^ 2 * B y y := mul_nonneg (sq_nonneg _) hy.le
    have hye : B y e = 0 := by
      by_contra hne
      have hpos := mul_pos (sq_pos_of_ne_zero hne) hxpos
      linarith
    exact (not_lt_of_ge (he y hye)) hy

/-- The reverse Cauchy–Schwarz inequality, including the zero quadratic-value
boundary case, follows from the one-positive-direction condition. -/
theorem bilinear_reverse_cauchy_schwarz
    (B : LinearMap.BilinForm ℝ E) (hB : ∀ x y, B x y = B y x) (e : E)
    (he : ∀ x, B x e = 0 → B x x ≤ 0)
    (x y : E) (hy : 0 ≤ B y y) : B x x * B y y ≤ (B x y) ^ 2 := by
  first
  | rcases hy.eq_or_lt with hyzero | hypos
    · rw [← hyzero, mul_zero]
      exact sq_nonneg _
    · let z : E := B y y • x - B x y • y
      have hzy : B z y = 0 := by
        simp only [z, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left]
        ring
      have hzz := bilinear_nonpos_on_positive_orthogonal B hB e he hypos hzy
      have hzexp : B z z = B y y * (B x x * B y y - (B x y) ^ 2) := by
        simp only [z, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right,
          LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hB y x]
        ring
      rw [hzexp] at hzz
      by_contra h
      have hpos := mul_pos hypos (sub_pos.mpr (lt_of_not_ge h))
      exact (not_lt_of_ge hzz) hpos

/-- A single positive reference vector is enough to test the hyperplane
condition by its reverse Cauchy–Schwarz inequality. -/
theorem bilinear_hyperplane_iff_reference_inequality
    (B : LinearMap.BilinForm ℝ E) (hB : ∀ x y, B x y = B y x) (e : E)
    (he : 0 < B e e) :
    (∀ x, B x e = 0 → B x x ≤ 0) ↔
      ∀ x, B x x * B e e ≤ (B x e) ^ 2 := by
  first
  | constructor
    · intro h x
      exact bilinear_reverse_cauchy_schwarz B hB e h x e he.le
    · intro h x hxe
      have hx := h x
      rw [hxe, zero_pow (by decide : 2 ≠ 0)] at hx
      by_contra hxx
      exact (not_lt_of_ge hx) (mul_pos (lt_of_not_ge hxx) he)

end VolumePolynomials

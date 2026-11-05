module

public import Mathlib.Algebra.Field.Basic

@[expose] public section

/-!
# Scalar core of the seven-hyperplane Gale obstruction

The coordinates are taken in the frame `B,D,R,S,O`. The vector `t` spans
the intersection of `AF` with `BDR`. The first four incidences put `x`
in `Bt` and `r = z-y` in `Dt`; the next two constrain `z` after projection
along `S`. The last incidence forces `z-x` to be a multiple of `S`.

All cancellation factors are explicit nonzero hypotheses inherited from
the independent four-sets and triples. The argument works over any field.
-/

namespace Papers.RationalityTen.GaleSevenAlgebra

variable {K : Type*} [Field K]

theorem projected_difference_zero
    (a b t₁ t₂ t₃ x₁ x₂ x₃ z₁ z₂ z₃ r₁ r₃ : K)
    (ht₃ : t₃ ≠ 0) (htransverse : a * t₂ - b * t₁ ≠ 0)
    (hx : t₃ * x₂ = t₂ * x₃)
    (hr : t₃ * r₁ = t₁ * r₃)
    (hxnon : x₂ ≠ 0 ∨ x₃ ≠ 0)
    (hrnon : r₁ ≠ 0 ∨ r₃ ≠ 0)
    (hz : x₂ * z₃ = x₃ * z₂)
    (hw : (z₁ - x₁) * r₃ = (z₃ - x₃) * r₁)
    (hlast : a * (z₂ - x₂) = b * (z₁ - x₁)) :
    z₁ = x₁ ∧ z₂ = x₂ ∧ z₃ = x₃ := by
  have hx₃ : x₃ ≠ 0 := by
    intro hzero
    have hx₂ : x₂ = 0 := (mul_eq_zero.mp (by simpa only [hzero, mul_zero] using hx)).resolve_left ht₃
    exact hxnon.elim (fun h => h hx₂) (fun h => h hzero)
  have hr₃ : r₃ ≠ 0 := by
    intro hzero
    have hr₁ : r₁ = 0 := (mul_eq_zero.mp (by simpa only [hzero, mul_zero] using hr)).resolve_left ht₃
    exact hrnon.elim (fun h => h hr₁) (fun h => h hzero)
  have hz₂ : t₃ * z₂ = t₂ * z₃ := by
    apply mul_left_cancel₀ hx₃
    calc
      x₃ * (t₃ * z₂) = t₃ * (x₃ * z₂) := by ac_rfl
      _ = t₃ * (x₂ * z₃) := by rw [hz]
      _ = (t₃ * x₂) * z₃ := by rw [mul_assoc]
      _ = (t₂ * x₃) * z₃ := by rw [hx]
      _ = x₃ * (t₂ * z₃) := by ac_rfl
  have hd₂ : t₃ * (z₂ - x₂) = t₂ * (z₃ - x₃) := by
    rw [mul_sub, mul_sub, hz₂, hx]
  have hd₁ : t₃ * (z₁ - x₁) = t₁ * (z₃ - x₃) := by
    apply mul_left_cancel₀ hr₃
    calc
      r₃ * (t₃ * (z₁ - x₁)) = t₃ * ((z₁ - x₁) * r₃) := by ac_rfl
      _ = t₃ * ((z₃ - x₃) * r₁) := by rw [hw]
      _ = (z₃ - x₃) * (t₃ * r₁) := by ac_rfl
      _ = (z₃ - x₃) * (t₁ * r₃) := by rw [hr]
      _ = r₃ * (t₁ * (z₃ - x₃)) := by ac_rfl
  have hd₃ : z₃ = x₃ := by
    have h : (a * t₂ - b * t₁) * (z₃ - x₃) = 0 := by
      calc
        _ = a * (t₂ * (z₃ - x₃)) - b * (t₁ * (z₃ - x₃)) := by
          rw [sub_mul, mul_assoc, mul_assoc]
        _ = a * (t₃ * (z₂ - x₂)) - b * (t₃ * (z₁ - x₁)) := by rw [← hd₂, ← hd₁]
        _ = t₃ * (a * (z₂ - x₂) - b * (z₁ - x₁)) := by
          conv_rhs => rw [mul_sub]
          congr 1 <;> ac_rfl
        _ = 0 := by rw [hlast, sub_self, mul_zero]
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left htransverse)
  have hz₁ : z₁ = x₁ := by
    have h : t₃ * (z₁ - x₁) = 0 := by simpa only [hd₃, sub_self, mul_zero] using hd₁
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left ht₃)
  have hz₂' : z₂ = x₂ := by
    have h : t₃ * (z₂ - x₂) = 0 := by simpa only [hd₃, sub_self, mul_zero] using hd₂
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left ht₃)
  exact ⟨hz₁, hz₂', hd₃⟩

end Papers.RationalityTen.GaleSevenAlgebra

module
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
@[expose] public section
namespace PaperVerification.ColdSpots

private theorem amgm3_at_minimum (x y z : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (hxz : x ≤ z) :
    27 * (x * y * z) ≤ (x + y + z) ^ 3 ∧
      ((x + y + z) ^ 3 = 27 * (x * y * z) ↔ x = y ∧ y = z) := by
  let u := y - x
  let v := z - x
  have hu : 0 ≤ u := sub_nonneg.mpr hxy
  have hv : 0 ≤ v := sub_nonneg.mpr hxz
  have hq : 0 ≤ u ^ 2 - u * v + v ^ 2 := by
    nlinarith [sq_nonneg (u-v), sq_nonneg u, sq_nonneg v]
  have hp : 0 ≤ 9 * x * (u ^ 2 - u * v + v ^ 2) := by positivity
  have hc : 0 ≤ (u + v) ^ 3 := pow_nonneg (add_nonneg hu hv) _
  have hi : (x+y+z)^3 - 27*(x*y*z) =
      9*x*(u^2-u*v+v^2) + (u+v)^3 := by dsimp [u,v]; ring
  refine ⟨by linarith, ?_⟩
  constructor
  · intro h
    have hz : (u+v)^3 = 0 := by linarith
    have huv : u+v = 0 := eq_zero_of_pow_eq_zero hz
    dsimp [u,v] at huv hu hv
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨rfl,rfl⟩
    ring

theorem three_term_amgm (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    27 * (x * y * z) ≤ (x + y + z) ^ 3 ∧
      ((x + y + z) ^ 3 = 27 * (x * y * z) ↔ x = y ∧ y = z) := by
  rcases le_total x y with hxy | hyx
  · rcases le_total x z with hxz | hzx
    · exact amgm3_at_minimum x y z hx hxy hxz
    · have h := amgm3_at_minimum z x y hz hzx (hzx.trans hxy)
      have he : (z=x ∧ x=y) ↔ (x=y ∧ y=z) := by constructor <;> rintro ⟨a,b⟩ <;> constructor <;> linarith
      simpa [add_comm,add_left_comm,add_assoc,mul_comm,mul_left_comm,mul_assoc,he] using h
  · rcases le_total y z with hyz | hzy
    · have h := amgm3_at_minimum y x z hy hyx hyz
      have he : (y=x ∧ x=z) ↔ (x=y ∧ y=z) := by constructor <;> rintro ⟨a,b⟩ <;> constructor <;> linarith
      simpa [add_comm,add_left_comm,add_assoc,mul_comm,mul_left_comm,mul_assoc,he] using h
    · have h := amgm3_at_minimum z x y hz (hzy.trans hyx) hzy
      have he : (z=x ∧ x=y) ↔ (x=y ∧ y=z) := by constructor <;> rintro ⟨a,b⟩ <;> constructor <;> linarith
      simpa [add_comm,add_left_comm,add_assoc,mul_comm,mul_left_comm,mul_assoc,he] using h

end PaperVerification.ColdSpots

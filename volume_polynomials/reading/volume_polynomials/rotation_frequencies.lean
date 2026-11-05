module

public import VolumePolynomials.HolonomyAngle
public import VolumePolynomials.FourierGeneratingSeries
public import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

@[expose] public section
noncomputable section

namespace VolumePolynomials

open scoped Topology

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

noncomputable def rotationUnit (θ : ℝ) (m : ℤ) : Circle :=
  AddCircle.toCircle (m • (θ : AddCircle Real.pi))

theorem rotationUnit_coe (θ : ℝ) (m : ℤ) :
    (rotationUnit θ m : ℂ) = rotationFrequency θ m := by
  first
  | rw [rotationUnit, ← QuotientAddGroup.mk_zsmul, AddCircle.toCircle_apply_mk,
      Circle.coe_exp, rotationFrequency]
    congr 1
    simp only [zsmul_eq_mul]
    push_cast
    field_simp [Real.pi_ne_zero] <;> ring

theorem angle_ratio_irrational {θ : ℝ} (hθ : Real.cos θ = 1 / 3) :
    Irrational (θ / Real.pi) := by
  first
  | rintro ⟨q, hq⟩
    apply Holonomy.angle_not_rational_multiple_pi hθ
    exact ⟨q, (div_eq_iff Real.pi_ne_zero).mp hq.symm⟩

theorem rotationUnit_dense {θ : ℝ} (hθ : Real.cos θ = 1 / 3) :
    DenseRange (rotationUnit θ) := by
  first
  | have hd : DenseRange (fun m : ℤ => m • (θ : AddCircle Real.pi)) :=
      AddCircle.denseRange_zsmul_coe_iff.mpr (angle_ratio_irrational hθ)
    let e := AddCircle.homeomorphCircle Real.pi_ne_zero
    have hcomp := e.surjective.denseRange.comp hd e.continuous
    change DenseRange (fun m : ℤ => AddCircle.toCircle (m • (θ : AddCircle Real.pi)))
    simpa only [Function.comp_def, e, AddCircle.homeomorphCircle_apply, rotationUnit] using hcomp

theorem rotationUnit_injective {θ : ℝ} (hθ : Real.cos θ = 1 / 3) :
    Function.Injective (rotationUnit θ) := by
  first
  | have hd : DenseRange (fun m : ℤ => m • (θ : AddCircle Real.pi)) :=
      AddCircle.denseRange_zsmul_coe_iff.mpr (angle_ratio_irrational hθ)
    have ho : addOrderOf (θ : AddCircle Real.pi) = 0 := AddCircle.denseRange_zsmul_iff.mp hd
    have hi : Function.Injective (fun m : ℤ => m • (θ : AddCircle Real.pi)) :=
      injective_zsmul_iff_not_isOfFinAddOrder.mpr (addOrderOf_eq_zero_iff.mp ho)
    exact (AddCircle.injective_toCircle Real.pi_ne_zero).comp hi

theorem rotationFrequency_injective {θ : ℝ} (hθ : Real.cos θ = 1 / 3) :
    Function.Injective (rotationFrequency θ) := by
  first
  | intro i j hij
    apply rotationUnit_injective hθ
    apply Subtype.coe_injective
    simpa only [rotationUnit_coe] using hij

end VolumePolynomials

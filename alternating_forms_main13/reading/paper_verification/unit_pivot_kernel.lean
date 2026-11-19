module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The kernel of a row with a unit pivot

This is the coordinate calculation for the kernel of the universal line
quotient on a projective chart. The distinguished coordinate is `none`.
All other coordinates are retained, while the pivot coordinate is their
negative weighted sum. The construction works over every commutative ring.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

namespace PaperVerification.UnitPivotKernel

variable (R : Type*) [CommRing R] (I : Type*) [Fintype I]

/-- A finite row as a linear map on coordinate vectors. -/
def row (a : Option I → R) : (Option I → R) →ₗ[R] R where
  toFun v := ∑ i, a i * v i
  map_add' v w := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' r v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact mul_left_comm (a i) r (v i)

@[simp]
lemma row_apply (a : Option I → R) (v : Option I → R) :
    row R I a v = a none * v none + ∑ i : I, a (some i) * v (some i) := by
  simp only [row, LinearMap.coe_mk, AddHom.coe_mk, Fintype.sum_option]

/-- The literal kernel is freely parametrized by the coordinates other
than the pivot, whenever the pivot coefficient equals one. -/
def kernelEquiv (a : Option I → R) (ha : a none = 1) :
    (row R I a).ker ≃ₗ[R] (I → R) where
  toFun v i := v.val (some i)
  invFun w :=
    ⟨fun i => i.elim (-(∑ j : I, a (some j) * w j)) w, by
      change row R I a _ = 0
      simp [row_apply, ha]⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    cases i with
    | some i => rfl
    | none =>
        have hv : v.val none + ∑ i : I, a (some i) * v.val (some i) = 0 := by
          simpa only [LinearMap.mem_ker, row_apply, ha, one_mul] using v.property
        exact (eq_neg_iff_add_eq_zero.mpr hv).symm
  right_inv w := rfl
  map_add' v w := rfl
  map_smul' r v := rfl

@[simp]
lemma kernelEquiv_apply (a : Option I → R) (ha : a none = 1)
    (v : (row R I a).ker) (i : I) : kernelEquiv R I a ha v i = v.val (some i) := rfl

@[simp]
lemma kernelEquiv_symm_some (a : Option I → R) (ha : a none = 1)
    (w : I → R) (i : I) : ((kernelEquiv R I a ha).symm w).val (some i) = w i := rfl

@[simp]
lemma kernelEquiv_symm_none (a : Option I → R) (ha : a none = 1)
    (w : I → R) : ((kernelEquiv R I a ha).symm w).val none =
      -(∑ i : I, a (some i) * w i) := rfl

/-- The same coordinate projection is bijective in any linearly equivalent
presentation of the kernel. This form applies directly to maps on sections
of actual module sheaves. -/
theorem kernel_projection_bijective
    {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (e : M ≃ₗ[R] (Option I → R))
    (a : Option I → R) (ha : a none = 1)
    (h : ∀ x, f x = 0 ↔ row R I a (e x) = 0) :
    Function.Bijective (fun x : f.ker => fun i => e x.val (some i)) := by
  let toRow : f.ker → (row R I a).ker := fun x =>
    ⟨e x.val, (h x.val).mp (LinearMap.mem_ker.mp x.property)⟩
  have htoRow : Function.Bijective toRow := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact e.injective (congrArg Subtype.val hxy)
    · intro v
      let x : f.ker := ⟨e.symm v.val, (h (e.symm v.val)).mpr (by
        rw [e.apply_symm_apply]
        exact LinearMap.mem_ker.mp v.property)⟩
      refine ⟨x, ?_⟩
      apply Subtype.ext
      exact e.apply_symm_apply v.val
  exact (kernelEquiv R I a ha).bijective.comp htoRow

end PaperVerification.UnitPivotKernel

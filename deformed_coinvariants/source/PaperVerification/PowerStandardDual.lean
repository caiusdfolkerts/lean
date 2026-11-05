module

public import PaperVerification.PowerStandardHarmonics
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RepresentationTheory.Basic

/-!
# Self-duality of the literal standard representation

On the coordinate-sum-zero subspace the ordinary coordinate dot product is
nondegenerate when the characteristic is zero. This identifies the standard
representation with its contragredient without a splitting-field hypothesis
or a character-table assertion.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Module
open scoped BigOperators

namespace PaperVerification.PowerStandardHarmonics

variable {K ι : Type*} [Field K] [Fintype ι]
local instance : DecidableEq ι := Classical.decEq ι
local notation "W" => standardSpace (K := K) (ι := ι)

def standardPermutation (σ : Equiv.Perm ι) : W ≃ₗ[K] W where
  toFun := permuteStandard σ
  invFun := permuteStandard σ.symm
  left_inv v := by
    apply Subtype.ext
    funext i
    simp only [permuteStandard, Equiv.symm_symm, Equiv.symm_apply_apply]
  right_inv v := by
    apply Subtype.ext
    funext i
    simp only [permuteStandard, Equiv.symm_symm, Equiv.apply_symm_apply]
  map_add' v w := by
    apply Subtype.ext
    rfl
  map_smul' a v := by
    apply Subtype.ext
    rfl

def standardRepresentation : Representation K (Equiv.Perm ι) W where
  toFun σ := (standardPermutation σ).toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    rfl
  map_mul' σ τ := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    rfl

def differenceVector (i j : ι) : W :=
  ⟨Pi.single i 1-Pi.single j 1, by
    simp [mem_standardSpace, Finset.sum_sub_distrib]⟩

theorem differenceVector_ne_zero (i j : ι) (hij : i ≠ j) :
    differenceVector (K := K) i j ≠ 0 := by
  intro hz
  have h := congrArg (fun v : W => v.val i) hz
  have hone : (1 : K) = 0 := by
    simpa only [differenceVector, Submodule.coe_zero, Pi.zero_apply, Pi.sub_apply,
      Pi.single_eq_same, Pi.single_eq_of_ne hij, sub_zero] using h
  exact one_ne_zero hone

def standardDot : W →ₗ[K] Module.Dual K W where
  toFun v :=
    { toFun := fun w => ∑ i, v.val i*w.val i
      map_add' := by
        intro w z
        simp only [Submodule.coe_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro a w
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
          Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring }
  map_add' v w := by
    apply LinearMap.ext
    intro z
    change (∑ i, (v.val i + w.val i) * z.val i) =
      (∑ i, v.val i * z.val i) + ∑ i, w.val i * z.val i
    simp only [add_mul, Finset.sum_add_distrib]
  map_smul' a v := by
    apply LinearMap.ext
    intro z
    change (∑ i, (a * v.val i) * z.val i) = a * ∑ i, v.val i * z.val i
    simp only [mul_assoc, Finset.mul_sum]

@[simp] theorem standardDot_apply (v w : W) :
    standardDot v w = ∑ i, v.val i*w.val i := rfl

theorem standardDot_difference (v : W) (i j : ι) :
    standardDot v (differenceVector i j) = v.val i-v.val j := by
  simp [standardDot_apply, differenceVector, mul_sub, Finset.sum_sub_distrib,
    Pi.single_apply]

theorem standardDot_injective [Nonempty ι] [CharZero K] :
    Function.Injective (standardDot : W →ₗ[K] Module.Dual K W) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  let b : ι := Classical.choice inferInstance
  have hcoord (i : ι) : v.val i = v.val b := by
    have he := LinearMap.congr_fun hv (differenceVector i b)
    rw [standardDot_difference] at he
    exact sub_eq_zero.mp he
  have hsum := (mem_standardSpace v.val).mp v.property
  simp_rw [hcoord] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hb : v.val b = 0 := (mul_eq_zero.mp hsum).resolve_left
    (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  apply Subtype.ext
  funext i
  exact (hcoord i).trans hb

def standardDualEquiv [Nonempty ι] [CharZero K] : W ≃ₗ[K] Module.Dual K W :=
  standardDot.linearEquivOfInjective standardDot_injective (Subspace.dual_finrank_eq.symm)

@[simp] theorem standardDualEquiv_apply [Nonempty ι] [CharZero K] (v w : W) :
    standardDualEquiv v w = ∑ i, v.val i*w.val i := rfl

theorem standardDot_permutation (σ : Equiv.Perm ι) (v w : W) :
    standardDot (standardPermutation σ v) (standardPermutation σ w) = standardDot v w := by
  change (∑ i, v.val (σ.symm i)*w.val (σ.symm i)) = ∑ i, v.val i*w.val i
  exact Equiv.sum_comp σ.symm (fun i : ι => v.val i * w.val i)

theorem standardDualEquiv_contragredient [Nonempty ι] [CharZero K]
    (σ : Equiv.Perm ι) (v w : W) :
    standardDualEquiv (standardPermutation σ v) w =
      standardDualEquiv v (standardPermutation σ.symm w) := by
  have he := standardDot_permutation σ v (standardPermutation σ.symm w)
  have hw : standardPermutation σ (standardPermutation σ.symm w) = w := by
    apply Subtype.ext
    funext i
    change w.val (σ (σ.symm i)) = w.val i
    rw [Equiv.apply_symm_apply]
  rw [hw] at he
  exact he

end PaperVerification.PowerStandardHarmonics

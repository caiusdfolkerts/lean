module

public import PaperVerification.PowerCoinvariantAction
public import PaperVerification.PowerStandardDual
public import Mathlib.RepresentationTheory.Intertwining

/-!
# Absence of the standard representation in high coinvariant degrees

The centered coordinate vector at the first index is fixed by the point
stabilizer. Its permutation orbit spans the actual coordinate-sum-zero space,
as proved by an explicit linear identity. Consequently an intertwiner into a
coinvariant piece of degree at least the number of variables vanishes on the
whole standard space. No character formula or representation table is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Representation
open scoped BigOperators

namespace PaperVerification.PowerCoinvariantStabilizer

open PowerStandardHarmonics

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}
local notation "W" => standardSpace (K := K) (ι := Fin (n+1))

def standardCentered (i : Fin (n+1)) : W :=
  ⟨((n+1 : ℕ) : K) • Pi.single i 1 - (1 : Fin (n+1) → K),by
    simp [mem_standardSpace,Finset.sum_sub_distrib,Pi.single_apply]⟩

theorem standardCentered_permutation (e : Equiv.Perm (Fin (n+1))) (i : Fin (n+1)) :
    standardPermutation e (standardCentered (K := K) i) = standardCentered (e i) := by
  apply Subtype.ext
  funext j
  simp [standardPermutation,permuteStandard,standardCentered,Pi.single_apply,Equiv.symm_apply_eq]

/-- The permutation orbit of a centered coordinate spans the entire literal
standard space. This identity supplies the spanning argument directly. -/
theorem standardCentered_sum (v : W) :
    (∑ i : Fin (n+1), v.val i • standardCentered (K := K) i) = ((n+1 : ℕ) : K) • v := by
  apply Subtype.ext
  funext j
  have hv := (mem_standardSpace v.val).mp v.property
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
    Pi.smul_apply, standardCentered, Pi.sub_apply, Pi.one_apply, smul_eq_mul]
  change (∑ i : Fin (n+1), v.val i *
      (((n+1 : ℕ) : K) * ((Pi.single i (1 : K) : Fin (n+1) → K) j) - 1)) =
        ((n+1 : ℕ) : K) * v.val j
  simp only [mul_sub,mul_one,Finset.sum_sub_distrib,hv,sub_zero]
  rw [Finset.sum_eq_single j]
  · simp only [Pi.single_eq_same,mul_one,one_mul,mul_comm]
  · intro i hi hij
    simp only [Pi.single_eq_of_ne (Ne.symm hij),mul_zero]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

/-- Every actual intertwiner from the standard representation to a homogeneous
ordinary coinvariant piece in degree at least `n+1` is zero. -/
theorem standard_intertwiner_eq_zero (d : ℕ) (hd : n+1 ≤ d)
    (f : IntertwiningMap (standardRepresentation (K := K) (ι := Fin (n+1)))
      (coinvariantDegreeRepresentation (K := K) (n := n) d)) : f = 0 := by
  have hf0 : f (standardCentered (K := K) (0 : Fin (n+1))) = 0 := by
    apply Subtype.ext
    apply point_stabilizer_fixed_eq_zero d hd _ (f (standardCentered (K := K) 0)).property
    intro e
    have h := congrArg Subtype.val
      (LinearMap.congr_fun (f.isIntertwining' (liftPermutation e))
        (standardCentered (K := K) 0))
    simp only [LinearMap.comp_apply, IntertwiningMap.toLinearMap_apply] at h
    have hs : standardRepresentation (K := K) (ι := Fin (n+1)) (liftPermutation e)
        (standardCentered (K := K) 0) = standardCentered (K := K) 0 := by
      change standardPermutation (liftPermutation e) (standardCentered (K := K) 0) = _
      rw [standardCentered_permutation,liftPermutation_zero]
    rw [hs] at h
    exact h.symm
  have hfi (i : Fin (n+1)) : f (standardCentered (K := K) i) = 0 := by
    have h := LinearMap.congr_fun (f.isIntertwining' (Equiv.swap 0 i))
      (standardCentered (K := K) 0)
    simp only [LinearMap.comp_apply, IntertwiningMap.toLinearMap_apply] at h
    change f (standardPermutation (Equiv.swap 0 i) (standardCentered (K := K) 0)) = _ at h
    rw [standardCentered_permutation,Equiv.swap_apply_left,hf0,map_zero] at h
    exact h
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  simp only [IntertwiningMap.zero_toLinearMap, LinearMap.zero_apply,
    IntertwiningMap.toLinearMap_apply]
  have h := congrArg f (standardCentered_sum v)
  simp only [map_sum,map_smul,hfi,smul_zero,Finset.sum_const_zero] at h
  have hr : ((n+1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have h' := congrArg (fun z => (((n+1 : ℕ) : K)⁻¹) • z) h.symm
  simpa only [smul_smul,inv_mul_cancel₀ hr,one_smul,smul_zero] using h'

theorem standard_intertwiner_finrank_eq_zero (d : ℕ) (hd : n+1 ≤ d) :
    Module.finrank K
      (IntertwiningMap (standardRepresentation (K := K) (ι := Fin (n+1)))
        (coinvariantDegreeRepresentation (K := K) (n := n) d)) = 0 := by
  letI : Subsingleton
      (IntertwiningMap (standardRepresentation (K := K) (ι := Fin (n+1)))
        (coinvariantDegreeRepresentation (K := K) (n := n) d)) :=
    ⟨fun f g => (standard_intertwiner_eq_zero d hd f).trans (standard_intertwiner_eq_zero d hd g).symm⟩
  exact Module.finrank_zero_of_subsingleton

end PaperVerification.PowerCoinvariantStabilizer

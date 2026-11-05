module

public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Data.Finset.Insert
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Abel

/-!
# Stable subspaces contain the distinct eigencomponents of their elements

This finite-support argument is valid without a finite-dimensional ambient
space. It is used for polynomial weighted homogeneous components.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open scoped BigOperators

namespace PaperVerification.Eigencomponents

variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A stable subspace contains each member of a finite sum of eigenvectors
with distinct eigenvalues whenever it contains their sum. -/
theorem mem_of_sum_mem (T : V →ₗ[K] V) (U : Submodule K V)
    (hU : ∀ x ∈ U, T x ∈ U) (μ : I → K) (hμ : Function.Injective μ)
    (s : Finset I) (v : I → V)
    (he : ∀ i ∈ s, T (v i) = μ i • v i)
    (hsum : ∑ i ∈ s, v i ∈ U) : ∀ i ∈ s, v i ∈ U := by
  classical
  induction s using Finset.induction_on generalizing v with
  | empty => simp
  | @insert a s ha ih =>
    have hEa : T (v a) = μ a • v a := he a (Finset.mem_insert_self _ _)
    have hEs : ∀ i ∈ s, T (v i) = μ i • v i :=
      fun i hi => he i (Finset.mem_insert_of_mem hi)
    let v' : I → V := fun i => (μ i - μ a) • v i
    have he' : ∀ i ∈ s, T (v' i) = μ i • v' i := by
      intro i hi
      dsimp [v']
      rw [map_smul, hEs i hi, smul_smul, smul_smul, mul_comm]
    have hTsum : T (∑ i ∈ s, v i) = ∑ i ∈ s, μ i • v i := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      exact hEs
    have htrans : (∑ i ∈ s, v' i) ∈ U := by
      have hm := U.sub_mem (hU _ hsum) (U.smul_mem (μ a) hsum)
      have heq : T (∑ i ∈ insert a s, v i) - μ a • (∑ i ∈ insert a s, v i) =
          ∑ i ∈ s, v' i := by
        rw [Finset.sum_insert ha, map_add, hEa, hTsum]
        simp only [v', sub_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, smul_add]
        abel
      rwa [heq] at hm
    have hrest' := ih v' he' htrans
    have hrest : ∀ i ∈ s, v i ∈ U := by
      intro i hi
      have hne : μ i - μ a ≠ 0 := sub_ne_zero.mpr
        (fun h => ha (hμ h ▸ hi))
      have hscaled := U.smul_mem (μ i - μ a)⁻¹ (hrest' i hi)
      simpa only [v', smul_smul, inv_mul_cancel₀ hne, one_smul] using hscaled
    have hva : v a ∈ U := by
      have hm := U.sub_mem hsum (U.sum_mem hrest)
      simpa only [Finset.sum_insert ha, add_sub_cancel_right] using hm
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hva
    · exact hrest i hi

end PaperVerification.Eigencomponents

module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section
noncomputable section
namespace Papers.Geometry
open Finset Set
variable {V ι : Type*} [AddCommGroup V] [Module ℝ V] [Fintype ι]

/-- A direct finite induction for the exact linear-form avoidance needed by
the exposed-edge perturbation. Every excluded value is an explicit root of
an affine function of one real scalar. -/
theorem exists_forall_linear_forms_ne_zero (forms : ι → V →ₗ[ℝ] ℝ)
    (hforms : ∀ i,∃ x,forms i x≠0) : ∃ x,∀ i,forms i x≠0 := by
  classical
  have aux : ∀ s : Finset ι,∃ x,∀ i∈s,forms i x≠0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨0,by simp⟩
    | @insert i s hi ih =>
      obtain ⟨x,hx⟩ := ih
      by_cases hix : forms i x≠0
      · refine ⟨x,?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hix
        · exact hx j hj
      · have hix0 : forms i x=0 := not_not.mp hix
        obtain ⟨y,hy⟩ := hforms i
        let bad : Finset ℝ := s.image fun j => -forms j x/forms j y
        obtain ⟨t,ht,hnotbad⟩ := (Set.Ioo_infinite (show (0 : ℝ)<1 by norm_num)).exists_notMem_finset bad
        refine ⟨x+t • y,?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · rw [map_add,map_smul,smul_eq_mul,hix0,zero_add]
          exact mul_ne_zero (ne_of_gt ht.1) hy
        · by_cases hjy : forms j y=0
          · simpa only [map_add,map_smul,smul_eq_mul,hjy,mul_zero,add_zero] using hx j hj
          · intro hz
            have htroot : -forms j x/forms j y=t := by
              apply (div_eq_iff hjy).mpr
              simp only [map_add,map_smul,smul_eq_mul] at hz
              linarith only [hz]
            exact hnotbad (Finset.mem_image.mpr ⟨j,hj,htroot⟩)
  obtain ⟨x,hx⟩ := aux Finset.univ
  exact ⟨x,fun i => hx i (Finset.mem_univ i)⟩

end Papers.Geometry

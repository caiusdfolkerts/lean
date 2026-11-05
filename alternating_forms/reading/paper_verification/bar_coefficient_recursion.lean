module

public import PaperVerification.ReducedBarBasis
public import Mathlib.LinearAlgebra.Finsupp.Defs

/-!
# Literal coefficient recursion for the normalized bar differential

These formulas retain the original multiplication coefficients and the
actual alternating bar signs. They are intended for the comparison of
diagonal bar cycles with the annihilator relations of a quadratic dual.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.BarCoefficientRecursion

open ReducedBarBasis AugmentedAlgebraBasis

variable {K A I : Type*} [CommRing K] [Ring A] [Algebra K A]
  (B : Module.Basis (Option I) K A)

local notation "W" => List I →₀ K

theorem prepend_nil (i : I) (z : W) : prepend i z []=0 := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero,Finsupp.zero_apply]
  | add z w hz hw => simp only [map_add,Finsupp.add_apply,hz,hw,add_zero]
  | single L c => simp only [prefix_single,Finsupp.single_apply,List.cons_ne_nil,if_false]

theorem prepend_cons (i j : I) (z : W) (L : List I) :
    prepend i z (j::L)=if i=j then z L else 0 := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero,Finsupp.zero_apply,ite_self]
  | add z w hz hw =>
      simp only [map_add,Finsupp.add_apply,hz,hw]
      split_ifs <;> simp only [add_zero]
  | single T c =>
      rw [prefix_single]
      by_cases h : i=j
      · subst j
        simp only [Finsupp.single_apply,List.cons.injEq,true_and,if_pos rfl,ite_true]
      · simp only [Finsupp.single_apply,List.cons.injEq,h,false_and,if_false]

theorem appendTail_nil (z : I →₀ K) (L : List I) : appendTail L z []=0 := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero,Finsupp.zero_apply]
  | add z w hz hw => simp only [map_add,Finsupp.add_apply,hz,hw,add_zero]
  | single i c => simp only [appendTail_single,Finsupp.single_apply,List.cons_ne_nil,if_false]

theorem appendTail_cons (z : I →₀ K) (L T : List I) (i : I) :
    appendTail L z (i::T)=if L=T then z i else 0 := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero,Finsupp.zero_apply,ite_self]
  | add z w hz hw =>
      simp only [map_add,Finsupp.add_apply,hz,hw]
      split_ifs <;> simp only [add_zero]
  | single j c =>
      rw [appendTail_single]
      by_cases h : L=T
      · subst T
        simp only [Finsupp.single_apply,List.cons.injEq,and_true,if_pos rfl,ite_true]
      · simp only [Finsupp.single_apply,List.cons.injEq,h,and_false,if_false]

theorem differentialBasis_nil_coefficient (L : List I) : differentialBasis B L []=0 := by
  cases L with
  | nil => rfl
  | cons a L =>
      cases L with
      | nil => simp only [differentialBasis,merge_single,mergeBasis,smul_zero,map_zero,
          sub_zero,Finsupp.zero_apply]
      | cons b L =>
          rw [differentialBasis,merge_single,one_smul,mergeBasis,Finsupp.sub_apply,
            appendTail_nil,prepend_nil,sub_zero]

/-- The first merge contributes the actual product coefficient; the
remaining merges carry precisely the negative of the shorter differential. -/
theorem differentialBasis_cons_cons (a b c : I) (L T : List I) :
    differentialBasis B (a::b::L) (c::T)=
      (if L=T then productCoefficients B a b c else 0)-
        (if a=c then differentialBasis B (b::L) T else 0) := by
  rw [differentialBasis,merge_single,one_smul,mergeBasis,Finsupp.sub_apply,
    appendTail_cons,prepend_cons]

def slice (i : I) : W →ₗ[K] W :=
  Finsupp.lcomapDomain (List.cons i) (fun _ _ h ↦ List.cons.inj h |>.2)

@[simp] theorem slice_apply (i : I) (z : W) (L : List I) :
    slice i z L=z (i::L) := rfl

@[simp] theorem slice_single_nil (i : I) (c : K) : slice i (Finsupp.single [] c)=0 := by
  apply Finsupp.ext
  intro L
  simp [slice_apply]

@[simp] theorem slice_single_cons (i j : I) (L : List I) (c : K) :
    slice i (Finsupp.single (j::L) c)=if j=i then Finsupp.single L c else 0 := by
  apply Finsupp.ext
  intro T
  rw [slice_apply]
  by_cases h : j=i
  · subst j
    simp only [Finsupp.single_apply,List.cons.injEq,true_and,if_pos rfl,ite_true]
  · simp only [Finsupp.single_apply,List.cons.injEq,h,false_and,if_false,Finsupp.zero_apply]

variable [Fintype I]

theorem merge_cons (a c : I) (z : W) (T : List I) :
    merge B a z (c::T)=∑ b : I,productCoefficients B a b c*z (b::T) := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero,Finsupp.zero_apply,mul_zero,Finset.sum_const_zero]
  | add z w hz hw =>
      simp only [map_add,Finsupp.add_apply,hz,hw,mul_add,Finset.sum_add_distrib]
  | single L t =>
      cases L with
      | nil => simp [merge_single,mergeBasis]
      | cons b L =>
          rw [merge_single,mergeBasis,Finsupp.smul_apply,smul_eq_mul,appendTail_cons]
          by_cases h : L=T
          · subst T
            simp [Finsupp.single_apply,List.cons.injEq,mul_comm]
          · simp only [h,if_false,mul_zero,Finsupp.single_apply,List.cons.injEq,
              and_false,Finset.sum_const_zero]

theorem differential_cons_slice (c : I) (z : W) (T : List I) :
    differential B z (c::T)=
      (∑ a : I,merge B a (slice a z) (c::T))-differential B (slice c z) T := by
  induction z using Finsupp.induction_linear with
  | zero =>
      simp only [map_zero,Finsupp.zero_apply,Finset.sum_const_zero,sub_zero]
  | add z w hz hw =>
      simp only [map_add,Finsupp.add_apply,hz,hw,Finset.sum_add_distrib]
      abel
  | single L t =>
      cases L with
      | nil => simp only [differential_single,differentialBasis,smul_zero,
          Finsupp.zero_apply,slice_single_nil,map_zero,Finset.sum_const_zero,sub_zero]
      | cons a L =>
          have hd := congrArg (fun w : W ↦ w (c::T))
            (differential_prefix B a (Finsupp.single L t))
          rw [prefix_single,Finsupp.sub_apply,prepend_cons] at hd
          have hs : (∑ j : I,merge B j (slice j (Finsupp.single (a::L) t)) (c::T))=
              merge B a (Finsupp.single L t) (c::T) := by
            calc
              _=merge B a (slice a (Finsupp.single (a::L) t)) (c::T) := by
                apply Finset.sum_eq_single a
                · intro j hj hja
                  rw [slice_single_cons,if_neg (Ne.symm hja),map_zero,Finsupp.zero_apply]
                · intro ha
                  exact (ha (Finset.mem_univ a)).elim
              _=merge B a (Finsupp.single L t) (c::T) := by
                rw [slice_single_cons,if_pos rfl]
          rw [hs,slice_single_cons]
          by_cases hac : a=c
          · subst c
            simpa only [if_pos rfl,ite_true] using hd
          · simpa only [hac,if_false,map_zero,Finsupp.zero_apply] using hd

/-- Coefficients of the actual differential are the original quadratic
multiplication coefficients followed by the recursive alternating tail. -/
theorem differential_cons (c : I) (z : W) (T : List I) :
    differential B z (c::T)=
      (∑ a : I,∑ b : I,productCoefficients B a b c*z (a::b::T))-
        differential B (slice c z) T := by
  rw [differential_cons_slice]
  simp_rw [merge_cons,slice_apply]

end PaperVerification.BarCoefficientRecursion

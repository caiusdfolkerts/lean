module

public import PaperVerification.FermionGradedQuotient
public import PaperVerification.FermionTensorQuotient

/-!
# Homogeneous two-sided ideals for arbitrary additive degree indices

The finite double decomposition proof applies in particular to the actual
exterior bidegree N × N, without reducing it to total degree.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace PaperVerification.Fermion

variable {R A Γ : Type*} [CommRing R] [Ring A] [Algebra R A]
  [AddMonoid Γ] [DecidableEq Γ]
variable (part : Γ → Submodule R A) [GradedAlgebra part]

theorem homogeneousIdeal_component_mul_left (I : TwoSidedIdeal A) (a b : A)
    (ha : ∀ j,GradedAlgebra.proj part j a∈I) (n : Γ) :
    GradedAlgebra.proj part n (b*a)∈I := by
  classical
  rw [←DirectSum.sum_support_decompose part b,←DirectSum.sum_support_decompose part a]
  simp only [Finset.sum_mul,Finset.mul_sum,map_sum]
  apply sum_mem
  intro j hj
  apply sum_mem
  intro i hi
  have hp : (DirectSum.decompose part b i : A)*(DirectSum.decompose part a j : A)
      ∈part (i+j) := SetLike.mul_mem_graded
        (DirectSum.decompose part b i).property (DirectSum.decompose part a j).property
  by_cases hn : i+j=n
  · rw [GradedAlgebra.proj_apply,DirectSum.decompose_of_mem_same part (hn ▸ hp)]
    exact I.mul_mem_left _ _ (ha j)
  · rw [GradedAlgebra.proj_apply,DirectSum.decompose_of_mem_ne part hp hn]
    exact I.zero_mem

theorem homogeneousIdeal_component_mul_right (I : TwoSidedIdeal A) (a b : A)
    (ha : ∀ j,GradedAlgebra.proj part j a∈I) (n : Γ) :
    GradedAlgebra.proj part n (a*b)∈I := by
  classical
  rw [←DirectSum.sum_support_decompose part a,←DirectSum.sum_support_decompose part b]
  simp only [Finset.sum_mul,Finset.mul_sum,map_sum]
  apply sum_mem
  intro j hj
  apply sum_mem
  intro i hi
  have hp : (DirectSum.decompose part a i : A)*(DirectSum.decompose part b j : A)
      ∈part (i+j) := SetLike.mul_mem_graded
        (DirectSum.decompose part a i).property (DirectSum.decompose part b j).property
  by_cases hn : i+j=n
  · rw [GradedAlgebra.proj_apply,DirectSum.decompose_of_mem_same part (hn ▸ hp)]
    exact I.mul_mem_right _ _ (ha i)
  · rw [GradedAlgebra.proj_apply,DirectSum.decompose_of_mem_ne part hp hn]
    exact I.zero_mem

theorem twoSided_span_multihomogeneous (generators : Set A)
    (hgen : ∀ g∈generators,∃ n,g∈part n) :
    ∀ a∈TwoSidedIdeal.span generators,∀ n,
      GradedAlgebra.proj part n a∈TwoSidedIdeal.span generators := by
  intro a ha
  induction ha using TwoSidedIdeal.span_induction with
  | mem g hg =>
      obtain ⟨i,hi⟩ := hgen g hg
      intro n
      by_cases hn : i=n
      · rw [GradedAlgebra.proj_apply,DirectSum.decompose_of_mem_same part (hn ▸ hi)]
        exact TwoSidedIdeal.subset_span hg
      · rw [GradedAlgebra.proj_apply,DirectSum.decompose_of_mem_ne part hi hn]
        exact TwoSidedIdeal.zero_mem _
  | zero =>
      intro n
      simpa only [map_zero] using (TwoSidedIdeal.span generators).zero_mem
  | add a b ha hb iha ihb =>
      intro n
      rw [map_add]
      exact (TwoSidedIdeal.span generators).add_mem (iha n) (ihb n)
  | neg a ha iha =>
      intro n
      rw [map_neg]
      exact (TwoSidedIdeal.span generators).neg_mem (iha n)
  | left_absorb b a ha iha =>
      exact homogeneousIdeal_component_mul_left part _ a b iha
  | right_absorb b a ha iha =>
      exact homogeneousIdeal_component_mul_right part _ a b iha

def multihomogeneousTwoSidedQuotientGrading (generators : Set A)
    (hgen : ∀ g∈generators,∃ n,g∈part n) :
    GradedAlgebra
      (gradedImagePart part ((TwoSidedIdeal.span generators).ringCon.mkₐ R)) :=
  gradedImageAlgebra part ((TwoSidedIdeal.span generators).ringCon.mkₐ R)
    (RingCon.mkₐ_surjective (α := R) _) (by
      intro n a ha
      have hamem : a∈TwoSidedIdeal.span generators := by
        change ((a : A) : (TwoSidedIdeal.span generators).ringCon.Quotient)=
          ((0 : A) : (TwoSidedIdeal.span generators).ringCon.Quotient) at ha
        exact Quotient.exact ha
      exact quotientMk_eq_zero_of_mem _ _
        (twoSided_span_multihomogeneous part generators hgen a hamem n))

end PaperVerification.Fermion


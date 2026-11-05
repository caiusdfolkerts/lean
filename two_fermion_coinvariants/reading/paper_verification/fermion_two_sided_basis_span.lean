module

public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Two-sided ideals as actual spans of basis multiples

The coefficient module underlying a generated two-sided ideal is spanned
by the generators multiplied on the left and right by ambient basis vectors.
This permits filtered module reduction without changing the quotient ideal.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion

open scoped BigOperators

variable {K A I J : Type*} [CommRing K] [Ring A] [Algebra K A]

def twoSidedIdealSubmodule (H : TwoSidedIdeal A) : Submodule K A where
  carrier := H
  zero_mem' := H.zero_mem
  add_mem' := H.add_mem
  smul_mem' a x hx := by
    rw [Algebra.smul_def]
    exact H.mul_mem_left _ _ hx

@[simp] theorem mem_twoSidedIdealSubmodule (H : TwoSidedIdeal A) (x : A) :
    x ∈ twoSidedIdealSubmodule (K := K) H ↔ x ∈ H := Iff.rfl

def basisRelationMultiple (b : Module.Basis I K A) (f : J → A) (z : I × J × I) : A :=
  b z.1 * f z.2.1 * b z.2.2

theorem arbitrary_multiple_mem_basis_span (b : Module.Basis I K A) (f : J → A)
    (a c : A) (j : J) :
    a * f j * c ∈ Submodule.span K (Set.range (basisRelationMultiple b f)) := by
  classical
  rw [← b.linearCombination_repr a,← b.linearCombination_repr c,
    Finsupp.linearCombination_apply,Finsupp.linearCombination_apply,Finsupp.sum,Finsupp.sum]
  simp only [Finset.sum_mul,Finset.mul_sum,smul_mul_assoc,mul_smul_comm,Finset.smul_sum,smul_smul]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.sum_mem
  intro k hk
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(k,j,i),rfl⟩)

theorem basis_span_mul_left (b : Module.Basis I K A) (f : J → A)
    (a x : A) (hx : x ∈ Submodule.span K (Set.range (basisRelationMultiple b f))) :
    a*x ∈ Submodule.span K (Set.range (basisRelationMultiple b f)) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨⟨i,j,k⟩,rfl⟩ := hx
      simpa only [basisRelationMultiple,mul_assoc] using
        arbitrary_multiple_mem_basis_span b f (a*b i) (b k) j
  | zero =>
      simpa only [mul_zero] using
        (Submodule.zero_mem (Submodule.span K (Set.range (basisRelationMultiple b f))))
  | add x y hx hy ihx ihy => simpa only [mul_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [mul_smul_comm] using Submodule.smul_mem _ c ih

theorem basis_span_mul_right (b : Module.Basis I K A) (f : J → A)
    (a x : A) (hx : x ∈ Submodule.span K (Set.range (basisRelationMultiple b f))) :
    x*a ∈ Submodule.span K (Set.range (basisRelationMultiple b f)) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨⟨i,j,k⟩,rfl⟩ := hx
      simpa only [basisRelationMultiple,mul_assoc] using
        arbitrary_multiple_mem_basis_span b f (b i) (b k*a) j
  | zero =>
      simpa only [zero_mul] using
        (Submodule.zero_mem (Submodule.span K (Set.range (basisRelationMultiple b f))))
  | add x y hx hy ihx ihy => simpa only [add_mul] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [smul_mul_assoc] using Submodule.smul_mem _ c ih

/-- The literal equality of the generated two-sided ideal and the coefficient
span of its left/right basis multiples. -/
theorem twoSidedIdealSubmodule_span (b : Module.Basis I K A) (f : J → A) :
    twoSidedIdealSubmodule (TwoSidedIdeal.span (Set.range f)) =
      Submodule.span K (Set.range (basisRelationMultiple b f)) := by
  classical
  let N := Submodule.span K (Set.range (basisRelationMultiple b f))
  let H : TwoSidedIdeal A := TwoSidedIdeal.mk' (N : Set A) N.zero_mem
    (fun hx hy ↦ N.add_mem hx hy) (fun hx ↦ N.neg_mem hx)
    (fun {x y} hy ↦ basis_span_mul_left b f x y hy)
    (fun {x y} hx ↦ basis_span_mul_right b f y x hx)
  have hH : TwoSidedIdeal.span (Set.range f) ≤ H := by
    apply TwoSidedIdeal.span_le.mpr
    rintro x ⟨j,rfl⟩
    apply (TwoSidedIdeal.mem_mk' _ _ _ _ _ _ _).mpr
    change f j∈Submodule.span K (Set.range (basisRelationMultiple b f))
    simpa only [one_mul,mul_one] using arbitrary_multiple_mem_basis_span b f 1 1 j
  apply le_antisymm
  · intro x hx
    have hh := hH hx
    exact (TwoSidedIdeal.mem_mk' _ _ _ _ _ _ _).mp hh
  · apply Submodule.span_le.mpr
    rintro x ⟨⟨i,j,k⟩,rfl⟩
    exact (TwoSidedIdeal.span (Set.range f)).mul_mem_right _ _
      ((TwoSidedIdeal.span (Set.range f)).mul_mem_left _ _ (TwoSidedIdeal.subset_span ⟨j,rfl⟩))

section LinearQuotient

variable {V E : Type*} [AddCommGroup V] [Module K V]

theorem span_image_eq_top_iff (q : A →ₗ[K] V) (hq : Function.Surjective q) (v : E → A) :
    Submodule.span K (Set.range (fun e ↦ q (v e))) = ⊤ ↔
      Submodule.span K (Set.range v) ⊔ q.ker = ⊤ := by
  let N := Submodule.span K (Set.range v)
  have hmap : N.map q = Submodule.span K (Set.range (fun e ↦ q (v e))) := by
    rw [Submodule.map_span,← Set.range_comp']
  constructor
  · intro h
    apply top_unique
    intro x hx
    have hqx : q x ∈ N.map q := by rw [hmap,h]; trivial
    obtain ⟨y,hy,he⟩ := hqx
    apply Submodule.mem_sup.mpr
    refine ⟨y,hy,x-y,?_,by abel⟩
    change q (x-y)=0
    rw [map_sub,he,sub_self]
  · intro h
    apply top_unique
    intro z hz
    obtain ⟨x,rfl⟩ := hq z
    have hx : x ∈ N ⊔ q.ker := by rw [h]; trivial
    obtain ⟨y,hy,k,hk,he⟩ := Submodule.mem_sup.mp hx
    rw [← hmap]
    refine ⟨y,hy,?_⟩
    rw [← he,map_add,LinearMap.mem_ker.mp hk,add_zero]

end LinearQuotient

end PaperVerification.Fermion

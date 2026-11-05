module

public import PaperVerification.FermionBlockNormalForm

/-!
# Exact multiplication normal forms in the initial quotient

For an actual homogeneous ambient vector, the initial quotient normal form
is exactly the component of its actual quotient normal form at the same
weight. This proves the structure-constant comparison needed at the zero
Rees fiber, rather than assuming that the two algebras have equal products.

-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion.BlockInitial

open BasisFiltered
open scoped BigOperators

variable {K P M N Q J : Type*} [CommRing K] [CommRing P] [Algebra K P]
  [AddCommGroup M] [Module P M] [Module K M] [IsScalarTower K P M]
  [AddCommGroup N] [Module K N] [AddCommGroup Q] [Module K Q] [Fintype J]
  {b : Module.Basis J P M} {weight : J → ℕ} {q : M →ₗ[K] Q}
  {D : J → Type*} [∀ j,Fintype (D j)]
  (h : TriangularPresentation (N := N) b weight q D)

theorem homogeneous_single (j : J) (p : P) :
    Homogeneous b weight (weight j) (p • b j) := by
  classical
  intro t ht
  by_cases htj : t=j
  · exact congrArg weight htj
  · exact (ht (by simp only [map_smul,Finsupp.smul_apply,Module.Basis.repr_self,
      Finsupp.single_eq_of_ne htj,smul_zero])).elim

theorem component_smul_scalar (r : ℕ) (c : K) (x : M) :
    component b weight r (c • x)=c • component b weight r x :=
  ((component b weight r).restrictScalars K).map_smul c x

namespace TriangularPresentation

theorem normalForm_lowerBound (r : ℕ) (x : M) (hx : LowerBound b weight r x) :
    LowerBound b weight r (h.normalForm x) := by
  intro j hj
  by_contra hn
  apply hj
  rw [h.normalForm_coordinate]
  apply Finset.sum_eq_zero
  intro e he
  rw [h.normalForm_coefficients_zero_below x r hx j (Nat.lt_of_not_ge hn) e,zero_smul]

/-- Only the same-weight actual quotient coefficients survive in the actual
initial quotient. -/
theorem initial_component_normal_form (r : ℕ) (x : M)
    (hx : Homogeneous b weight r x) :
    (initialMin b weight q.ker).mkQ x=
      ∑ z:Sigma D,if weight z.1=r then
        h.basis.repr (q x) z • (initialMin b weight q.ker).mkQ (h.representative z) else 0 := by
  classical
  let I := initialMin b weight q.ker
  have hb : LowerBound b weight r x := fun i hi ↦ (hx i hi).ge
  have hn := h.normalForm_lowerBound r x hb
  have hsub : LowerBound b weight r (x-h.normalForm x) :=
    (lowerSubmodule b weight r).sub_mem hb hn
  have hmem : component b weight r (x-h.normalForm x)∈I :=
    Submodule.subset_span ⟨x-h.normalForm x,h.subtract_normalForm_mem_kernel x,r,hsub,rfl⟩
  have hz := (Submodule.Quotient.mk_eq_zero I).mpr hmem
  change I.mkQ (component b weight r (x-h.normalForm x))=0 at hz
  rw [map_sub,component_of_homogeneous b weight hx,if_pos rfl,map_sub] at hz
  have he : I.mkQ x=I.mkQ (component b weight r (h.normalForm x)) := sub_eq_zero.mp hz
  rw [he]
  change I.mkQ (component b weight r
    (∑ z:Sigma D,h.basis.repr (q x) z • h.representative z))=_
  rw [map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro z hz
  rw [component_smul_scalar,map_smul]
  have hv : Homogeneous b weight (weight z.1) (h.representative z) :=
    homogeneous_single (b := b) (weight := weight) z.1 (h.polynomial z.1 z.2)
  rw [component_of_homogeneous b weight hv]
  by_cases hzr : weight z.1=r
  · rw [if_pos hzr,if_pos hzr.symm]
  · rw [if_neg hzr,if_neg (Ne.symm hzr),map_zero,smul_zero]

end TriangularPresentation

end PaperVerification.Fermion.BlockInitial

module

public import PaperVerification.FermionFilteredModuleSpanning
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Bases of the actual homogeneous images in a quotient

The quotient degree space is defined as the image of the original homogeneous
space.  Stability of the actual kernel under homogeneous projection proves
that its basis is exactly the selected homogeneous quotient vectors.

-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion.BasisFiltered

open scoped BigOperators

variable {R M Q I E : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup Q] [Module R Q]
  (b : Module.Basis I R M) (w : I → ℕ)

def homogeneousPiece (d : ℕ) : Submodule R M where
  carrier := {x | Homogeneous b w d x}
  zero_mem' := by intro i hi; exact (hi (by simp)).elim
  add_mem' := by
    intro x y hx hy i hi
    by_cases hxi : b.repr x i=0
    · apply hy i
      simpa only [map_add,Finsupp.add_apply,hxi,zero_add] using hi
    · exact hx i hxi
  smul_mem' := by
    intro c x hx i hi
    apply hx i
    intro hz
    exact hi (by simp only [map_smul,Finsupp.smul_apply,hz,smul_zero])

variable [Fintype E]

theorem quotientPiece_eq_basisSpan
    (q : M →ₗ[R] Q) (B : Module.Basis E R Q) (v : E → M) (degree : E → ℕ)
    (hv : ∀ e, Homogeneous b w (degree e) (v e)) (hB : ∀ e,q (v e)=B e)
    (hker : ∀ d x,x ∈ q.ker → component b w d x ∈ q.ker) (d : ℕ) :
    (homogeneousPiece b w d).map q =
      Submodule.span R (Set.range (fun e : {e : E // degree e=d} ↦ B e.val)) := by
  classical
  apply le_antisymm
  · rintro y ⟨x,hx,rfl⟩
    let z : M := ∑ e, B.repr (q x) e • v e
    have hqz : q z=q x := by
      simpa only [z,map_sum,map_smul,hB] using B.sum_repr (q x)
    have hr : x-z ∈ q.ker := by
      rw [LinearMap.mem_ker,map_sub,hqz,sub_self]
    have hproj := LinearMap.mem_ker.mp (hker d (x-z) hr)
    have hxx : component b w d x=x := by
      rw [component_of_homogeneous b w hx,if_pos rfl]
    rw [map_sub,hxx,map_sub,sub_eq_zero] at hproj
    rw [hproj]
    simp only [z,map_sum,map_smul]
    apply Submodule.sum_mem
    intro e he
    rw [component_of_homogeneous b w (hv e)]
    by_cases hd : d=degree e
    · rw [if_pos hd,hB]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨e,hd.symm⟩,rfl⟩)
    · simp only [if_neg hd,map_zero,smul_zero]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro y ⟨e,rfl⟩
    rcases e with ⟨e,he⟩
    refine ⟨v e,?_,hB e⟩
    change Homogeneous b w d (v e)
    simpa only [he] using hv e

/-- The selected vectors form a basis of the actual image degree space. -/
def quotientPieceBasis
    (q : M →ₗ[R] Q) (B : Module.Basis E R Q) (v : E → M) (degree : E → ℕ)
    (hv : ∀ e, Homogeneous b w (degree e) (v e)) (hB : ∀ e,q (v e)=B e)
    (hker : ∀ d x,x ∈ q.ker → component b w d x ∈ q.ker) (d : ℕ) :
    Module.Basis {e : E // degree e=d} R ((homogeneousPiece b w d).map q) :=
  (Module.Basis.span (B.linearIndependent.comp Subtype.val Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (quotientPiece_eq_basisSpan b w q B v degree hv hB hker d).symm)

@[simp] theorem quotientPieceBasis_coe
    (q : M →ₗ[R] Q) (B : Module.Basis E R Q) (v : E → M) (degree : E → ℕ)
    (hv : ∀ e, Homogeneous b w (degree e) (v e)) (hB : ∀ e,q (v e)=B e)
    (hker : ∀ d x,x ∈ q.ker → component b w d x ∈ q.ker) (d : ℕ)
    (e : {e : E // degree e=d}) :
    (quotientPieceBasis b w q B v degree hv hB hker d e : Q)=B e.val := by
  simp only [quotientPieceBasis,Module.Basis.map_apply,LinearEquiv.coe_ofEq_apply,
    Module.Basis.coe_span_apply,Function.comp_apply]

end PaperVerification.Fermion.BasisFiltered

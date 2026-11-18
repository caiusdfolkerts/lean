module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Algebra.DirectSum.Module

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set
open scoped BigOperators DirectSum

namespace Unimodular.BasisPartition

variable {R M I J : Type*} [Ring R] [AddCommGroup M] [Module R M]

def block (b : Module.Basis I R M) (f : I → J) (c : J) : Submodule R M :=
  Submodule.span R (b '' {i | f i = c})

theorem mem_block_iff (b : Module.Basis I R M) (f : I → J) (c : J) (x : M) :
    x ∈ block b f c ↔ ∀ i, f i ≠ c → b.repr x i = 0 := by
  classical
  rw [block, b.mem_span_image]
  constructor
  · intro hx i hi
    by_contra hn
    exact hi (hx (Finsupp.mem_support_iff.mpr hn))
  · intro hx i hi
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hi) (hx i hn)

/-- Partitioning the indices of an actual basis gives independent submodules.
The statement permits arbitrary component types and infinite bases. -/
theorem blocks_independent (b : Module.Basis I R M) (f : I → J) :
    iSupIndep (block b f) := by
  classical
  intro c
  apply Submodule.disjoint_def.mpr
  intro x hx hxother
  apply b.repr.injective
  ext i
  simp only [map_zero, Finsupp.zero_apply]
  by_cases hi : f i = c
  · have hle : (⨆ d, ⨆ (_ : d ≠ c), block b f d) ≤ LinearMap.ker (b.coord i) := by
      apply iSup_le
      intro d
      apply iSup_le
      intro hd y hy
      change b.repr y i = 0
      exact (mem_block_iff b f d y).mp hy i (fun hid => hd (hid.symm.trans hi))
    exact hle hxother
  · exact (mem_block_iff b f c x).mp hx i hi

theorem blocks_span (b : Module.Basis I R M) (f : I → J) :
    (⨆ c, block b f c) = ⊤ := by
  apply top_unique
  calc
    ⊤ = Submodule.span R (Set.range b) := b.span_eq.symm
    _ ≤ ⨆ c, block b f c := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact (le_iSup (block b f) (f i)) (Submodule.subset_span ⟨i, rfl, rfl⟩)

theorem blocks_internal [DecidableEq J] (b : Module.Basis I R M) (f : I → J) :
    DirectSum.IsInternal (block b f) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (blocks_independent b f) (blocks_span b f)

section Finite

variable [Fintype J] [DecidableEq J]

/-- The canonical sum of the original submodule inclusions, promoted to an
equivalence only after its actual internal-direct-sum property is proved. -/
def productEquiv (A : J → Submodule R M) (hA : DirectSum.IsInternal A) :
    (∀ j, A j) ≃ₗ[R] M :=
  (DFinsupp.linearEquivFunOnFintype (R := R) (M := fun j => A j)).symm.trans
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap A) hA)

theorem productEquiv_apply (A : J → Submodule R M) (hA : DirectSum.IsInternal A)
    (x : ∀ j, A j) : productEquiv A hA x = ∑ j, (x j : M) := by
  classical
  let z : ⨁ j, A j :=
    (DFinsupp.linearEquivFunOnFintype (R := R) (M := fun j => A j)).symm x
  change DirectSum.coeLinearMap A z = _
  have hz : ∑ j, DirectSum.of (fun j => A j) j (z j) = z := by
    simpa using DirectSum.sum_univ_of z
  calc
    DirectSum.coeLinearMap A z =
        DirectSum.coeLinearMap A (∑ j, DirectSum.of (fun j => A j) j (z j)) :=
      congrArg (DirectSum.coeLinearMap A) hz.symm
    _ = ∑ j, (z j : M) := by simp only [map_sum, DirectSum.coeLinearMap_of]
    _ = ∑ j, (x j : M) := rfl

theorem productEquiv_symm_of_mem (A : J → Submodule R M)
    (hA : DirectSum.IsInternal A) {j : J} {x : M} (hx : x ∈ A j) :
    (productEquiv A hA).symm x j = ⟨x, hx⟩ :=
  hA.ofBijective_coeLinearMap_of_mem hx

theorem productEquiv_symm_of_mem_ne (A : J → Submodule R M)
    (hA : DirectSum.IsInternal A) {j k : J} (hjk : j ≠ k)
    {x : M} (hx : x ∈ A j) : (productEquiv A hA).symm x k = 0 :=
  hA.ofBijective_coeLinearMap_of_mem_ne hjk hx

end Finite
end Unimodular.BasisPartition

#print axioms Unimodular.BasisPartition.blocks_internal
#print axioms Unimodular.BasisPartition.productEquiv_apply
#print axioms Unimodular.BasisPartition.productEquiv_symm_of_mem
#print axioms Unimodular.BasisPartition.productEquiv_symm_of_mem_ne
#check "UNIMODULAR_BASIS_PARTITION_EOF_V2"

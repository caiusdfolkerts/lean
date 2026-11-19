module

public import ToricPower.CWRelativeSubcomplex

/-! # A smaller genuine subcomplex inside a larger one

The nested construction retains the ambient characteristic maps at
both steps. In particular it can put a closed complement inside an
actual linear-slice subcomplex before taking relative cellular chains.
-/

@[expose] public noncomputable section

open Set Topology

namespace ToricPower

variable {X : Type*} [TopologicalSpace X] [T2Space X]
  {C : Set X} [CWComplex C]

theorem subcomplex_cell_mono (A B : CWComplex.Subcomplex C) (included : A ≤ B)
    (n : ℕ) (i : A.I n) : i.val ∈ B.I n := by
  obtain ⟨x,point⟩ := RelCWComplex.openCell_nonempty n i.val
  by_contra absent
  exact (B.disjoint_openCell_subcomplex_of_notMem absent).notMem_of_mem_left point
    (included (A.openCell_subset_of_mem i.property point))

/-- The actual smaller subcomplex as a subcomplex of the actual larger
one, with literally the same characteristic disks. -/
def subcomplexWithin (A B : CWComplex.Subcomplex C) (included : A ≤ B) :
    CWComplex.Subcomplex (B : Set X) where
  carrier := A
  I n := {i : B.I n | i.val ∈ A.I n}
  closed' := A.closed
  union' := by
    rw [empty_union]
    apply Subset.antisymm
    · intro x inside
      obtain ⟨n,hx⟩ := mem_iUnion.mp inside
      obtain ⟨i,point⟩ := mem_iUnion.mp hx
      exact A.openCell_subset_of_mem i.property point
    · intro x inside
      rw [← CWComplex.Subcomplex.union (E := A)] at inside
      obtain ⟨n,inside⟩ := mem_iUnion.mp inside
      obtain ⟨i,point⟩ := mem_iUnion.mp inside
      exact mem_iUnion.mpr ⟨n,mem_iUnion.mpr
        ⟨⟨⟨i.val,subcomplex_cell_mono A B included n i⟩,i.property⟩,point⟩⟩

@[simp]
theorem subcomplexWithin_carrier (A B : CWComplex.Subcomplex C) (included : A ≤ B) :
    (subcomplexWithin A B included : Set X) = A := rfl

end ToricPower

end

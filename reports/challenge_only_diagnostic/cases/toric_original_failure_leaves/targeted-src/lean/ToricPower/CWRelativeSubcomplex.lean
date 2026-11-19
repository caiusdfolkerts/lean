module

public import Mathlib.Topology.CWComplex.Classical.Subcomplex

/-!
# The CW structure of a pair

For a CW complex `C` and a subcomplex `A`, the pair `(C,A)` has precisely
the cells of `C` which do not belong to `A`.  This construction retains
the original characteristic maps.  It is data, rather than a global
instance, because the same underlying space carries both its absolute
and its relative CW structure.
-/

public section

noncomputable section

open Set Metric Topology
open Topology.CWComplex

namespace ToricPower

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {C : Set X} [CWComplex C]

/-- The relative CW structure obtained by placing a subcomplex in the
base. Its characteristic maps are unchanged. -/
@[expose, instance_reducible]
def relativeToSubcomplex (A : CWComplex.Subcomplex C) : RelCWComplex C (A : Set X) where
  cell n := {i : cell C n // i ∉ A.I n}
  map n i := map (C := C) n i.1
  source_eq n i := source_eq (C := C) n i.1
  continuousOn n i := continuousOn (C := C) n i.1
  continuousOn_symm n i := continuousOn_symm (C := C) n i.1
  pairwiseDisjoint' := by
    intro ⟨n, i⟩ _ ⟨m, j⟩ _ different
    change Disjoint (openCell n i.1) (openCell m j.1)
    apply disjoint_openCell_of_ne
    exact Function.injective_id.sigma_map (fun _ => Subtype.val_injective) |>.ne different
  disjointBase' n i := A.disjoint_openCell_subcomplex_of_notMem i.2
  mapsTo n i := by
    classical
    obtain ⟨J, covers⟩ := cellFrontier_subset_finite_closedCell (C := C) n i.1
    refine ⟨fun m => Finset.preimage (J m) Subtype.val Subtype.val_injective.injOn, ?_⟩
    intro x hx
    have image_mem := covers ⟨x, hx, rfl⟩
    simp only [mem_iUnion, exists_prop] at image_mem
    obtain ⟨m, lower, j, member, point⟩ := image_mem
    by_cases inBase : j ∈ A.I m
    · exact Or.inl (A.closedCell_subset_of_mem inBase point)
    · apply Or.inr
      simp only [mem_iUnion, exists_prop, Finset.mem_preimage]
      exact ⟨m, lower, ⟨j, inBase⟩, member, point⟩
  closed' S subset closedPieces := by
    apply (CWComplex.closed C S subset).mpr
    intro n i
    by_cases inBase : i ∈ A.I n
    · have contained := A.closedCell_subset_of_mem inBase
      have equality : S ∩ closedCell n i = (S ∩ (A : Set X)) ∩ closedCell n i := by
        ext x
        exact ⟨fun hx => ⟨⟨hx.1, contained hx.2⟩, hx.2⟩,
          fun hx => ⟨hx.1.1, hx.2⟩⟩
      rw [equality]
      exact closedPieces.2.inter isClosed_closedCell
    · exact closedPieces.1 n ⟨i, inBase⟩
  isClosedBase := A.closed
  union' := by
    apply subset_antisymm
    · apply union_subset A.subset_complex
      exact iUnion₂_subset fun n i => closedCell_subset_complex n i.1
    · intro x hx
      have covered := hx
      rw [← CWComplex.union (C := C)] at covered
      simp only [mem_iUnion] at covered
      obtain ⟨n, i, point⟩ := covered
      by_cases inBase : i ∈ A.I n
      · exact Or.inl (A.closedCell_subset_of_mem inBase point)
      · exact Or.inr (mem_iUnion.2 ⟨n, mem_iUnion.2 ⟨⟨i, inBase⟩, point⟩⟩)

end ToricPower

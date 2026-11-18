module

public import ToricPower.ArrangementUniversalCells
public import Mathlib.Topology.MetricSpace.Bounded

/-! # Finitely many genuine periodic cells in every bounded region

Finiteness follows from local finiteness of the original closed-cell
family and compactness of the closure of the bounded region. No finite
replacement of the universal arrangement is introduced.
-/

@[expose] public noncomputable section

open Set Topology

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)

theorem boundedRegion_cells_finite (region : Set (Fin n → ℝ))
    (bounded : Bornology.IsBounded region) (q : ℕ) :
    Finite {c : Cell (augmentedForms A) q // cellCenter (augmentedForms A) c ∈ region} := by
  let F : ((Fin s ⊕ Fin n → ℤ) × Set (Fin s ⊕ Fin n)) → Set (Fin n → ℝ) :=
    fun p => closedCell (augmentedForms A) p.1 p.2
  have locallyFinite : LocallyFinite F :=
    closedCells_locallyFinite (augmentedForms A)
      (fun j => (augmentedForms A j).continuous_of_finiteDimensional)
  have finite : Set.Finite {p | (F p ∩ closure region).Nonempty} :=
    locallyFinite.finite_nonempty_inter_compact bounded.isCompact_closure
  let f : {c : Cell (augmentedForms A) q // cellCenter (augmentedForms A) c ∈ region} →
      {p | (F p ∩ closure region).Nonempty} := fun c =>
    ⟨c.val.val,cellCenter (augmentedForms A) c.val,
      cell_subset_closedCell _ _ _ (cellCenter_mem _ c.val),subset_closure c.property⟩
  letI : Finite {p | (F p ∩ closure region).Nonempty} := finite.to_subtype
  exact Finite.of_injective f (by
    intro c d equal
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : {p | (F p ∩ closure region).Nonempty} => z.val) equal)

end ToricPower.IntegralArrangement

end

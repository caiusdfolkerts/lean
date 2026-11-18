module

public import ToricPower.ArrangementIncidenceCategory

/-! # The actual universal cells and their face category

These definitions and elementary center identities are extracted unchanged
from `WeightedIncidenceGeometry` and `ArrangementCostalkCells`. Keeping them
independent of the relative cellular-chain machinery lets the local geometry
use the actual face category without importing costalk computations.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Set
open scoped Classical

namespace ToricPower.IntegralArrangement

section Universal
variable {n s : ℕ} (A : Fin s → Fin n → ℤ)

/-- Every actual cell of the periodic arrangement, in its own dimension. -/
def UniversalIncidenceObject := Σ d, Cell (augmentedForms A) d

def universalIncidenceClosedCell (c : UniversalIncidenceObject A) : Set (Fin n → ℝ) :=
  closedCell (augmentedForms A) c.2.val.1 c.2.val.2

instance universalIncidencePreorder : Preorder (UniversalIncidenceObject A) where
  le c d := universalIncidenceClosedCell A c ⊆ universalIncidenceClosedCell A d
  le_refl _ := Set.Subset.rfl
  le_trans _ _ _ := Set.Subset.trans

end Universal

section Centers
variable {n s : ℕ} (matrix : Fin s → Fin n → ℤ)

@[simp]
theorem cellCenter_ceilingVector {q : ℕ} (c : Cell (augmentedForms matrix) q) :
    ceilingVector (augmentedForms matrix) (cellCenter (augmentedForms matrix) c) = c.val.1 := by
  funext i
  exact ceil_eq_of_mem_cell _ _ _ (cellCenter_mem _ c) i

@[simp]
theorem cellCenter_integralIndices {q : ℕ} (c : Cell (augmentedForms matrix) q) :
    integralIndices (augmentedForms matrix) (cellCenter (augmentedForms matrix) c) = c.val.2 :=
  integralIndices_eq_of_mem_cell _ _ _ (cellCenter_mem _ c)

end Centers

end ToricPower.IntegralArrangement

end

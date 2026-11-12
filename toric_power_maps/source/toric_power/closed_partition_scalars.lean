module

public import Mathlib.LinearAlgebra.DFinsupp
public import ToricPower.OpenClosedScalar

/-!
# Closed scalar coefficients partitioned by their unique component

The index set may be infinite. At any point of the closed support there
is exactly one component, so its scalar coefficient is the genuine
algebraic direct sum of all component coefficients.
-/

@[expose] public noncomputable section

open scoped Classical

namespace ToricPower.MorseCoefficients

variable (k : Type) [CommRing k] {I : Type} (p : Prop) (label : p → I)

def closedPartitionPredicate (i : I) : Prop := ∃ h : p, label h = i

/-- The whole direct sum, with its original scalar action. -/
def closedPartitionEquiv :
    (Π₀ i : I, PLift (closedPartitionPredicate p label i) → k) ≃ₗ[k] (PLift p → k) where
  toFun x h := x (label h.down) ⟨h.down,rfl⟩
  invFun f := if h : p then DFinsupp.single (label h) (fun _ => f ⟨h⟩) else 0
  left_inv x := by
    by_cases hp : p
    · apply DFinsupp.ext
      intro i
      funext h
      obtain ⟨h',equal⟩ := h.down
      have same : label hp = i := (congrArg label (Subsingleton.elim hp h')).trans equal
      subst i
      simp only [dif_pos hp,DFinsupp.single_eq_same]
    · apply DFinsupp.ext
      intro i
      funext h
      exact (hp h.down.choose).elim
  right_inv f := by
    funext h
    simp only [dif_pos h.down,DFinsupp.single_eq_same]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem closedPartitionEquiv_apply
    (x : Π₀ i : I, PLift (closedPartitionPredicate p label i) → k) (h : PLift p) :
    closedPartitionEquiv k p label x h = x (label h.down) ⟨h.down,rfl⟩ := rfl

/-- Evaluating at the named component is independent of the equality
proof used to identify that component. -/
theorem closedPartition_component_value
    (x : Π₀ i : I, PLift (closedPartitionPredicate p label i) → k)
    (h : p) {i : I} (equal : label h = i) :
    x i ⟨h,equal⟩ = x (label h) ⟨h,rfl⟩ := by
  cases equal
  rfl

end ToricPower.MorseCoefficients

end

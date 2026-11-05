module

public import PaperVerification.IsotropicAttractingCount
public import PaperVerification.PluckerWeightOrder

/-!
# The exact size of the finite affine paving

The budget is one precisely for an independent original pivot and zero for
an empty stratum. Its sum counts every nonempty cell once, independently of
the arbitrary tie-breaking in the finite Plücker weight order.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.IsotropicAttractingCharts

open PaperVerification.AlternatingForms
open PaperVerification.IsotropicAttractingCoordinates
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def cellBudget (k s m : ℕ) : ℕ := by
  classical
  exact if h : m < pivotCount s (2*k+1) then
    if IndependentPivots (indexEmbedding (weightOrderedPivots s (2*k+1) ⟨m,h⟩)) then 1 else 0
  else 0

theorem cellBudget_at (k s : ℕ) (i : Fin (pivotCount s (2*k+1))) :
    cellBudget k s i.val =
      if IndependentPivots (indexEmbedding (weightOrderedPivots s (2*k+1) i)) then 1 else 0 := by
  classical
  simp only [cellBudget, dite_eq_left i.isLt]

def orderedIndependentEquiv (k s : ℕ) :
    {i : Fin (pivotCount s (2*k+1)) //
      IndependentPivots (indexEmbedding (weightOrderedPivots s (2*k+1) i))} ≃
        IndependentPluckerIndices k s :=
  Equiv.subtypeEquivOfSubtype
    (p := fun p : PluckerIndex s (2*k+1) => IndependentPivots (indexEmbedding p))
    (weightOrderedPivots s (2*k+1))

theorem sum_cellBudget (k s : ℕ) (hs : s ≤ k+1) :
    ∑ m ∈ Finset.range (pivotCount s (2*k+1)), cellBudget k s m =
      Nat.choose (2*k+2-s) s := by
  classical
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [cellBudget_at]
  have hc : (∑ i : Fin (pivotCount s (2*k+1)),
      if IndependentPivots (indexEmbedding (weightOrderedPivots s (2*k+1) i)) then 1 else 0) =
        Nat.card {i : Fin (pivotCount s (2*k+1)) //
          IndependentPivots (indexEmbedding (weightOrderedPivots s (2*k+1) i))} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp
  rw [hc, Nat.card_congr (orderedIndependentEquiv k s)]
  exact card_independentPluckerIndices k s hs

end PaperVerification.IsotropicAttractingCharts

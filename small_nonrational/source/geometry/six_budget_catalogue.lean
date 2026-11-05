module
prelude
public import SixBudgetRows1
public import SixBudgetRows2
public import SixBudgetRows3
public import SixBudgetRows4
public import SixBudgetRows5
public import SixBudgetRows6

@[expose] public section

set_option maxRecDepth 10000

/-!
# Exact coverage by all 478 six-facet numerical budgets

`complete` is the finite-list endpoint used by the geometric adapter.  It
retains all seven six-vertex facet types, including every prism and pentagonal
pyramid branch.  The catalogue is an exact reduction of the proved complete
enumerator; no assertion from the Python producer is imported as a premise.
-/

namespace Papers.RationalityTen.SixBudgetEnumeration

def catalogue : List Row :=
  literalRows1 ++ literalRows2 ++ literalRows3 ++ literalRows4 ++ literalRows5 ++ literalRows6

theorem enumerated_eq_catalogue : enumeratedRows = catalogue := by
  change rowsForTotal 1 ++ (rowsForTotal 2 ++ (rowsForTotal 3 ++
    (rowsForTotal 4 ++ (rowsForTotal 5 ++ (rowsForTotal 6 ++ []))))) = catalogue
  rw [rowsForTotal1_eq, rowsForTotal2_eq, rowsForTotal3_eq,
    rowsForTotal4_eq, rowsForTotal5_eq, rowsForTotal6_eq]
  rfl

theorem catalogue_length : catalogue.length = 478 := by decide +kernel

/-- Complete coverage of the unrestricted natural-number budget predicate. -/
theorem complete (B : Row) (h : B.Admissible) : B ∈ catalogue := by
  rw [← enumerated_eq_catalogue]
  exact enumerated_complete B h

#print axioms complete
#print axioms catalogue_length

end Papers.RationalityTen.SixBudgetEnumeration

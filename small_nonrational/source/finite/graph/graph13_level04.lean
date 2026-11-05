module
prelude
public import Graph13Level04Part000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level04
open Papers.RationalityTen
open ConcreteGrowth GraphCatalogueCore GraphCatalogueCheck GraphCatalogueData FiniteChecks
abbrev count : Nat := 11
noncomputable def dispatch : Table (Nat → (State 45)) :=
(.leaf Part000.lookup)
noncomputable def lookup (i : Nat) : (State 45) := (dispatch.get i) i
noncomputable def test (i : Nat) : Bool := stateCheck (lookup i)
theorem checked : Interval test 0 11 := by
  intro i hlo hhi
  have hlocal := Part000.checked i (by omega) (by omega)
  simpa only [test, lookup, dispatch, Table.get, Part000.test] using hlocal
noncomputable def entry (i : Fin count) : (State 45) := lookup i.val

theorem entry_checked (i : Fin count) : stateCheck (entry i) = true :=
  checked i.val (Nat.zero_le _) i.isLt

end Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level04

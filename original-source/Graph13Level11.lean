module
prelude
public import Graph13Level11Part000
public import Graph13Level11Part001
public import Graph13Level11Part002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level11
open Papers.RationalityTen
open ConcreteGrowth GraphCatalogueCore GraphCatalogueCheck GraphCatalogueData FiniteChecks
abbrev count : Nat := 4319
noncomputable def dispatch : Table (Nat → (State 45)) :=
(.branch 2048
 (.leaf Part000.lookup)
 (.branch 4096
 (.leaf Part001.lookup)
 (.leaf Part002.lookup)))
noncomputable def lookup (i : Nat) : (State 45) := (dispatch.get i) i
noncomputable def test (i : Nat) : Bool := stateCheck (lookup i)
theorem checked : Interval test 0 4319 := by
  intro i hlo hhi
  by_cases h0 : i < 2048
  · have hlocal := Part000.checked i (by omega) (by omega)
    simpa only [test, lookup, dispatch, Table.get, if_pos h0, Part000.test] using hlocal
  · by_cases h1 : i < 4096
    · have hlocal := Part001.checked i (by omega) (by omega)
      simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_pos h1, Part001.test] using hlocal
    · have hlocal := Part002.checked i (by omega) (by omega)
      simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_neg h1, Part002.test] using hlocal
noncomputable def entry (i : Fin count) : (State 45) := lookup i.val

theorem entry_checked (i : Fin count) : stateCheck (entry i) = true :=
  checked i.val (Nat.zero_le _) i.isLt

end Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level11

module
prelude
public meta import LowerSchemas.FiniteGraph
public import Graph13Level12Part000
public import Graph13Level12Part001
public import Graph13Level12Part002
public import Graph13Level12Part003
public import Graph13Level12Part004

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level12
open Papers.RationalityTen
open ConcreteGrowth GraphCatalogueCore GraphCatalogueCheck GraphCatalogueData FiniteChecks
abbrev count : Nat := 8333
noncomputable def dispatch : Table (Nat → (State 45)) :=
(.branch 4096
 (.branch 2048
 (.leaf Part000.lookup)
 (.leaf Part001.lookup))
 (.branch 6144
 (.leaf Part002.lookup)
 (.branch 8192
 (.leaf Part003.lookup)
 (.leaf Part004.lookup))))
cert_lookup_3
cert_test_3
theorem checked : Interval test 0 8333 := by
  intro i hlo hhi
  by_cases h0 : i < 4096
  · by_cases h1 : i < 2048
    · have hlocal := Part000.checked i (by omega) (by omega)
      simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_pos h1, Part000.test] using hlocal
    · have hlocal := Part001.checked i (by omega) (by omega)
      simpa only [test, lookup, dispatch, Table.get, if_pos h0, if_neg h1, Part001.test] using hlocal
  · by_cases h1 : i < 6144
    · have hlocal := Part002.checked i (by omega) (by omega)
      simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_pos h1, Part002.test] using hlocal
    · by_cases h2 : i < 8192
      · have hlocal := Part003.checked i (by omega) (by omega)
        simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_neg h1, if_pos h2, Part003.test] using hlocal
      · have hlocal := Part004.checked i (by omega) (by omega)
        simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_neg h1, if_neg h2, Part004.test] using hlocal
cert_entry
cert_entry_checked
end Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level12

module
prelude
public meta import LowerSchemas.FiniteGraph
public import Graph13Step08Part000
public import Graph13Step08Part001
public import Graph13Step08Part002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Step08
open Papers.RationalityTen
open ConcreteGrowth GraphCatalogueCore GraphCatalogueCheck GraphCatalogueData FiniteChecks
abbrev count : Nat := 367
noncomputable def dispatch : Table (Nat → Nat) :=
(.branch 128
 (.leaf Part000.lookup)
 (.branch 256
 (.leaf Part001.lookup)
 (.leaf Part002.lookup)))
cert_lookup_6
cert_test 08 367 09
theorem checked : Interval test 0 367 := by
  intro i hlo hhi
  by_cases h0 : i < 128
  · have hlocal := Part000.checked i (by omega) (by omega)
    simpa only [test, lookup, dispatch, Table.get, if_pos h0, Part000.test] using hlocal
  · by_cases h1 : i < 256
    · have hlocal := Part001.checked i (by omega) (by omega)
      simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_pos h1, Part001.test] using hlocal
    · have hlocal := Part002.checked i (by omega) (by omega)
      simpa only [test, lookup, dispatch, Table.get, if_neg h0, if_neg h1, Part002.test] using hlocal
cert_entry_2
cert_choices 367 883
cert_choices_checked 367 08 09
cert_covers_step 08 8 09 9
end Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Step08

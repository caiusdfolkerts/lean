module
prelude
public meta import LowerSchemas.FiniteGraph
public import Graph13Level09Part000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level09
open Papers.RationalityTen
open ConcreteGrowth GraphCatalogueCore GraphCatalogueCheck GraphCatalogueData FiniteChecks
abbrev count : Nat := 883
noncomputable def dispatch : Table (Nat → (State 45)) :=
(.leaf Part000.lookup)
cert_lookup_3
cert_test_3
cert_checked_2 883
cert_entry
cert_entry_checked
end Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level09

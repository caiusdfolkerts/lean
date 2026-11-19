module
prelude
public meta import LowerSchemas.FiniteGraph
public import Graph13Step05Part000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Step05
open Papers.RationalityTen
open ConcreteGrowth GraphCatalogueCore GraphCatalogueCheck GraphCatalogueData FiniteChecks
abbrev count : Nat := 25
noncomputable def dispatch : Table (Nat → Nat) :=
(.leaf Part000.lookup)
cert_lookup_6
cert_test 05 25 06
cert_checked_2 25
cert_entry_2
cert_choices 25 62
cert_choices_checked 25 05 06
cert_covers_step 05 5 06 6
end Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Step05

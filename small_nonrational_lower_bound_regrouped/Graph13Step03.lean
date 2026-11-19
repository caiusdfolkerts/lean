module
prelude
public meta import LowerSchemas.FiniteGraph
public import Graph13Step03Part000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Step03
open Papers.RationalityTen
open ConcreteGrowth GraphCatalogueCore GraphCatalogueCheck GraphCatalogueData FiniteChecks
abbrev count : Nat := 5
noncomputable def dispatch : Table (Nat → Nat) :=
(.leaf Part000.lookup)
cert_lookup_6
cert_test 03 5 04
cert_checked_2 5
cert_entry_2
cert_choices 5 11
cert_choices_checked 5 03 04
cert_covers_step 03 3 04 4
end Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Step03

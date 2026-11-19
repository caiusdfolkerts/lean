module
prelude
public meta import LowerSchemas.FiniteGraph
public import Graph13Step02Part000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Step02
open Papers.RationalityTen
open ConcreteGrowth GraphCatalogueCore GraphCatalogueCheck GraphCatalogueData FiniteChecks
abbrev count : Nat := 2
noncomputable def dispatch : Table (Nat → Nat) :=
(.leaf Part000.lookup)
cert_lookup_6
cert_test 02 2 03
cert_checked_2 2
cert_entry_2
cert_choices 2 5
cert_choices_checked 2 02 03
cert_covers_step 02 2 03 3
end Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Step02

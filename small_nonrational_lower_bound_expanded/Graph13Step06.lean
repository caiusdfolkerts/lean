module
prelude
public meta import LowerSchemas.FiniteGraph
public import Graph13Step06Part000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Step06
open Papers.RationalityTen
open ConcreteGrowth GraphCatalogueCore GraphCatalogueCheck GraphCatalogueData FiniteChecks
abbrev count : Nat := 62
noncomputable def dispatch : Table (Nat → Nat) :=
(.leaf Part000.lookup)
cert_lookup_6
cert_test 06 62 07
cert_checked_2 62
cert_entry_2
cert_choices 62 149
cert_choices_checked 62 06 07
cert_covers_step 06 6 07 7
end Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Step06

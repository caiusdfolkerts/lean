module
prelude
public meta import LowerSchemas.FiniteGraph
public import Graph13Step07Part000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Step07
open Papers.RationalityTen
open ConcreteGrowth GraphCatalogueCore GraphCatalogueCheck GraphCatalogueData FiniteChecks
abbrev count : Nat := 149
noncomputable def dispatch : Table (Nat → Nat) :=
(.leaf Part000.lookup)
cert_lookup_6
cert_test 07 149 08
cert_checked_2 149
cert_entry_2
cert_choices 149 367
cert_choices_checked 149 07 08
cert_covers_step 07 7 08 8
end Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Step07

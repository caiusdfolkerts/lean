module
prelude
public meta import LowerSchemas.FiniteGraph
public import Graph13Step00Part000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Step00
open Papers.RationalityTen
open ConcreteGrowth GraphCatalogueCore GraphCatalogueCheck GraphCatalogueData FiniteChecks
abbrev count : Nat := 1
noncomputable def dispatch : Table (Nat → Nat) :=
(.leaf Part000.lookup)
cert_lookup_6
cert_test 00 1 01
cert_checked_2 1
cert_entry_2
cert_choices 1 1
cert_choices_checked 1 00 01
cert_covers_step 00 0 01 1
end Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Step00

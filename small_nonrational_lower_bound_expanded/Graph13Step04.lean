module
prelude
public meta import LowerSchemas.FiniteGraph
public import Graph13Step04Part000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Step04
open Papers.RationalityTen
open ConcreteGrowth GraphCatalogueCore GraphCatalogueCheck GraphCatalogueData FiniteChecks
abbrev count : Nat := 11
noncomputable def dispatch : Table (Nat → Nat) :=
(.leaf Part000.lookup)
cert_lookup_6
cert_test 04 11 05
cert_checked_2 11
cert_entry_2
cert_choices 11 25
cert_choices_checked 11 04 05
cert_covers_step 04 4 05 5
end Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Step04

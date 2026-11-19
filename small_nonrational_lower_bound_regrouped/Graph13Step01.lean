module
prelude
public meta import LowerSchemas.FiniteGraph
public import Graph13Step01Part000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Step01
open Papers.RationalityTen
open ConcreteGrowth GraphCatalogueCore GraphCatalogueCheck GraphCatalogueData FiniteChecks
abbrev count : Nat := 1
noncomputable def dispatch : Table (Nat → Nat) :=
(.leaf Part000.lookup)
cert_lookup_6
cert_test 01 1 02
cert_checked_2 1
cert_entry_2
cert_choices 1 2
cert_choices_checked 1 01 02
cert_covers_step 01 1 02 2
end Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Step01

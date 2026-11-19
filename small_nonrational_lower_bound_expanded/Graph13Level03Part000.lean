module
prelude
public meta import LowerSchemas.FiniteGraph
public import GraphCatalogueData

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level03.Part000
open Papers.RationalityTen
open ConcreteGrowth GraphCatalogueCore GraphCatalogueCheck GraphCatalogueData FiniteChecks
noncomputable def table : Table (State 45) :=
(.branch 2
 (.branch 1
 (.leaf ⟨[34,37,39],704374636544⟩)
 (.leaf ⟨[38,41,42],6871947673600⟩))
 (.branch 3
 (.leaf ⟨[41,42,44],24189255811072⟩)
 (.branch 4
 (.leaf ⟨[41,43,44],28587302322176⟩)
 (.leaf ⟨[42,43,44],30786325577728⟩))))
cert_lookup_2
cert_test_3
cert_checked 0 5 5
theorem checked : Interval test 0 5 :=
  checked_0
end Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level03.Part000

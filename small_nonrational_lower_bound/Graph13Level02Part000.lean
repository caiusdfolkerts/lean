module
prelude
public meta import LowerSchemas.FiniteGraph
public import GraphCatalogueData

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level02.Part000
open Papers.RationalityTen
open ConcreteGrowth GraphCatalogueCore GraphCatalogueCheck GraphCatalogueData FiniteChecks
noncomputable def table : Table (State 45) :=
(.branch 1
 (.leaf ⟨[41,42],6597069766656⟩)
 (.leaf ⟨[43,44],26388279066624⟩))
cert_lookup_2
cert_test_3
cert_checked 0 2 2
theorem checked : Interval test 0 2 :=
  checked_0
end Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level02.Part000

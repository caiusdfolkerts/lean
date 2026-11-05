module
prelude
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
noncomputable def lookup (i : Nat) : (State 45) := table.get i
noncomputable def test (i : Nat) : Bool := stateCheck (lookup i)
theorem checked_0 : Interval test 0 2 :=
  interval_of_check test 0 2 (by decide +kernel)

theorem checked : Interval test 0 2 :=
  checked_0
end Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level02.Part000

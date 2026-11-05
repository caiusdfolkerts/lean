module
prelude
public import GraphCatalogueData

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level00.Part000
open Papers.RationalityTen
open ConcreteGrowth GraphCatalogueCore GraphCatalogueCheck GraphCatalogueData FiniteChecks
noncomputable def table : Table (State 45) :=
(.leaf ⟨[],0⟩)
noncomputable def lookup (i : Nat) : (State 45) := table.get i
noncomputable def test (i : Nat) : Bool := stateCheck (lookup i)
theorem checked_0 : Interval test 0 1 :=
  interval_of_check test 0 1 (by decide +kernel)

theorem checked : Interval test 0 1 :=
  checked_0
end Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level00.Part000

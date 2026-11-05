module
prelude
public import GraphCatalogueData

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level04.Part000
open Papers.RationalityTen
open ConcreteGrowth GraphCatalogueCore GraphCatalogueCheck GraphCatalogueData FiniteChecks
noncomputable def table : Table (State 45) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟨[23,28,32,35],38931529728⟩)
 (.leaf ⟨[29,34,37,39],704911507456⟩))
 (.branch 3
 (.leaf ⟨[34,38,40,42],5789615915008⟩)
 (.branch 4
 (.leaf ⟨[34,38,41,42],6889127542784⟩)
 (.leaf ⟨[38,40,42,43],14568529068032⟩))))
 (.branch 8
 (.branch 6
 (.leaf ⟨[40,41,42,43],16492674416640⟩)
 (.branch 7
 (.leaf ⟨[34,37,39,44],18296560680960⟩)
 (.leaf ⟨[38,41,42,44],24464133718016⟩)))
 (.branch 9
 (.leaf ⟨[38,41,43,44],28862180229120⟩)
 (.branch 10
 (.leaf ⟨[35,42,43,44],30820685316096⟩)
 (.leaf ⟨[41,42,43,44],32985348833280⟩)))))
noncomputable def lookup (i : Nat) : (State 45) := table.get i
noncomputable def test (i : Nat) : Bool := stateCheck (lookup i)
theorem checked_0 : Interval test 0 11 :=
  interval_of_check test 0 11 (by decide +kernel)

theorem checked : Interval test 0 11 :=
  checked_0
end Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level04.Part000

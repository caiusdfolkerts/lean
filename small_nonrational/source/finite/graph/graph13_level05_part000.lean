module
prelude
public import GraphCatalogueData

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level05.Part000
open Papers.RationalityTen
open ConcreteGrowth GraphCatalogueCore GraphCatalogueCheck GraphCatalogueData FiniteChecks
noncomputable def table : Table (State 45) :=
(.branch 12
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ⟨[8,15,21,26,30],1142980864⟩)
 (.branch 2
 (.leaf ⟨[16,23,28,32,35],38931595264⟩)
 (.leaf ⟨[23,29,33,37,39],696329961472⟩)))
 (.branch 4
 (.leaf ⟨[23,29,34,37,39],704919896064⟩)
 (.branch 5
 (.leaf ⟨[29,34,37,39,42],5102958018560⟩)
 (.leaf ⟨[29,34,38,40,42],5790152785920⟩))))
 (.branch 9
 (.branch 7
 (.leaf ⟨[34,38,39,40,42],6339371728896⟩)
 (.branch 8
 (.leaf ⟨[29,34,38,41,42],6889664413696⟩)
 (.leaf ⟨[34,37,39,41,42],7301444403200⟩)))
 (.branch 10
 (.leaf ⟨[37,38,39,41,42],7559142440960⟩)
 (.branch 11
 (.leaf ⟨[29,33,35,42,43],13237626077184⟩)
 (.leaf ⟨[34,38,40,42,43],14585708937216⟩)))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ⟨[30,40,41,42,43],16493748158464⟩)
 (.branch 14
 (.leaf ⟨[38,40,41,42,43],16767552323584⟩)
 (.leaf ⟨[23,28,32,35,44],17631117574144⟩)))
 (.branch 16
 (.leaf ⟨[29,34,37,39,44],18297097551872⟩)
 (.branch 17
 (.leaf ⟨[34,38,40,42,44],23381801959424⟩)
 (.leaf ⟨[34,38,41,42,44],24481313587200⟩))))
 (.branch 21
 (.branch 19
 (.leaf ⟨[34,37,39,43,44],27092653703168⟩)
 (.branch 20
 (.leaf ⟨[37,39,41,43,44],29274497089536⟩)
 (.leaf ⟨[26,30,42,43,44],30787466428416⟩)))
 (.branch 23
 (.branch 22
 (.leaf ⟨[34,35,42,43,44],30837865185280⟩)
 (.leaf ⟨[38,40,42,43,44],32160715112448⟩))
 (.branch 24
 (.leaf ⟨[38,41,42,43,44],33260226740224⟩)
 (.leaf ⟨[40,41,42,43,44],34084860461056⟩))))))
noncomputable def lookup (i : Nat) : (State 45) := table.get i
noncomputable def test (i : Nat) : Bool := stateCheck (lookup i)
theorem checked_0 : Interval test 0 16 :=
  interval_of_check test 0 16 (by decide +kernel)

theorem checked_16 : Interval test 16 25 :=
  interval_of_check test 16 9 (by decide +kernel)

theorem checked : Interval test 0 25 :=
  (interval_append test 0 16 25
  checked_0
  checked_16)
end Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level05.Part000

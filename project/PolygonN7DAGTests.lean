module
prelude
public import PolygonN7DAGData

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.PolygonGrowth.N7
open Papers.RationalityTen GrowthDAG SparseGrowthDAG GrowthPruning FiniteChecks

noncomputable def candidateTest (i : Nat) : Bool :=
  let a := Fin.ofNat 290 i
  (ridgeList a).all fun q => has (candidates q) a

noncomputable def nodeTest (i : Nat) : Bool :=
  WitnessGrowthDAG.nodeCheck ridgeList candidates compatible kind quota terminals nodes (Fin.ofNat 11426 i)

end Papers.RationalityTen.PolygonGrowth.N7

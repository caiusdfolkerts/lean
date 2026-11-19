module

public import FinitePolygonTemplates
public import PolygonN7DAG
public import PolygonDAGSemantics
public import FiniteChecks

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.ConcretePolygonClassification.N7
open Papers.RationalityTen PolygonBoundaryCatalogue BoundarySearch PolygonDAGSemantics
open GrowthDAG SparseGrowthDAG GrowthPruning

noncomputable def edgeCode : (Fin 7 × Fin 7) ≃ Fin 49 := finProdFinEquiv

noncomputable def ridgeDataTest (index : ℕ) : Bool :=
  let a := Fin.ofNat 290 index
  decide ((PolygonGrowth.N7.ridgeList a).toFinset = (FiniteCycleCandidates.N7.cells a).edges.image edgeCode)

noncomputable def compatibilityTest (index : ℕ) : Bool :=
  let a := Fin.ofNat 290 index
  decide (∀ b : Fin 290, PolygonBoundaryCatalogue.compatible (FiniteCycleCandidates.N7.cells a) (FiniteCycleCandidates.N7.cells b) →
    PolygonGrowth.N7.compatible a b = true)

noncomputable def terminalTest (index : ℕ) : Bool :=
  let j := Fin.ofNat 3796 index
  terminalCheck FiniteCycleCandidates.N7.cells FiniteCycleCandidates.N7.templates (PolygonGrowth.N7.terminals j)
    (PolygonGrowth.N7.targetTemplate j) (decode (by decide : 0 < 7) (PolygonGrowth.N7.permutationCode j))


end Papers.RationalityTen.ConcretePolygonClassification.N7

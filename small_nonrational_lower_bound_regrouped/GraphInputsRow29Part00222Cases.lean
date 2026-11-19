module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00222Checked
public import GraphInputsRow29Part00222Metadata
public import GraphInputsRow29Part00222Frames
public import GraphInputsRow29Part00222Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch120
public import GraphCoverageBatch154
public import GraphInputsRow29Part00222Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00222
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 29) 30238203449344 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 30238203449344 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12043 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 30238203449344
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch120.candidate12043_checked

theorem record000_result : Result (29, 30238203449344) :=
  of_direct_small 29 30238203449344 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00222.record000.direct_core, record000_parameters, record000_coverage⟩
#print axioms record000_result

certified_graph_case record001 29 30238314860672 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15451 14

certified_graph_case record002 29 30241150472448 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12044 14

certified_graph_case record003 29 30241158860800 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12045 14

certified_graph_case record004 29 30241166987520 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12046 14

certified_graph_case record005 29 30241175375872 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12047 14

certified_graph_case record006 29 30241418907776 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12048 14

certified_graph_case record007 29 30241435422848 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12049 14

certified_graph_case record008 29 30241670303760 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12050 14

certified_graph_case record009 29 30242240463616 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12051 14

certified_graph_case record010 29 30242508898944 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12052 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00222

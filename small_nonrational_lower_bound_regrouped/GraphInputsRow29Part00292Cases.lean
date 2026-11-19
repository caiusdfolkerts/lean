module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00292Checked
public import GraphInputsRow29Part00292Metadata
public import GraphInputsRow29Part00292Frames
public import GraphInputsRow29Part00292Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch123
public import GraphInputsRow29Part00292Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00292
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 34763498848256 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12357 14

certified_graph_case record001 29 34789235230736 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12358 14

certified_graph_case record002 29 34790308839940 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12359 14

theorem record003_parameters : Parameters record003 (rowOfCode 29) 34840774838528 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34840774838528 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12360 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 34840774838528
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch123.candidate12360_checked

theorem record003_result : Result (29, 34840774838528) :=
  of_direct_small 29 34840774838528 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00292.record003.direct_core, record003_parameters, record003_coverage⟩
#print axioms record003_result

certified_graph_case record004 29 34875159609344 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12361 14

certified_graph_case record005 29 34892331089920 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12362 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00292

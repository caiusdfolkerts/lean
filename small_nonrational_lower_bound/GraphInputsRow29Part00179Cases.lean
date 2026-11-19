module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00179Checked
public import GraphInputsRow29Part00179Metadata
public import GraphInputsRow29Part00179Frames
public import GraphInputsRow29Part00179Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch118
public import GraphCoverageBatch152
public import GraphInputsRow29Part00179Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00179
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 25994215964928 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15282 14

certified_graph_case record001 29 25994886906368 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15283 14

certified_graph_case record002 29 25997437178112 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15284 14

certified_graph_case record003 29 26117981929472 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11883 14

certified_graph_case record004 29 26122545283072 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11884 14

certified_graph_case record005 29 26126286196992 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15285 14

theorem record006_parameters : Parameters record006 (rowOfCode 29) 26130983948288 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 26130983948288 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11885 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 26130983948288
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch118.candidate11885_checked

theorem record006_result : Result (29, 26130983948288) :=
  of_direct_small 29 26130983948288 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00179.record006.direct_core, record006_parameters, record006_coverage⟩
#print axioms record006_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00179

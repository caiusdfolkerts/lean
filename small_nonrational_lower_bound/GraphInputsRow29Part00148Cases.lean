module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00148Checked
public import GraphInputsRow29Part00148Metadata
public import GraphInputsRow29Part00148Frames
public import GraphInputsRow29Part00148Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch117
public import GraphCoverageBatch151
public import GraphInputsRow29Part00148Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00148
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 24573655548160 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15186 14

certified_graph_case record001 29 24578361393152 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15187 14

certified_graph_case record002 29 24584594423808 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11754 14

certified_graph_case record003 29 24590835417088 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15188 14

certified_graph_case record004 29 24591103819776 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11755 14

certified_graph_case record005 29 24638216241408 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15189 14

theorem record006_parameters : Parameters record006 (rowOfCode 29) 24642513338368 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24642513338368 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11756 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24642513338368
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch117.candidate11756_checked

theorem record006_result : Result (29, 24642513338368) :=
  of_direct_small 29 24642513338368 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00148.record006.direct_core, record006_parameters, record006_coverage⟩
#print axioms record006_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00148

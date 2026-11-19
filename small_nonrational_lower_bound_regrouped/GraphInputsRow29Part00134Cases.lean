module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00134Checked
public import GraphInputsRow29Part00134Metadata
public import GraphInputsRow29Part00134Frames
public import GraphInputsRow29Part00134Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch116
public import GraphCoverageBatch150
public import GraphInputsRow29Part00134Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00134
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 22875801125440 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15072 14

certified_graph_case record001 29 22910160863776 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15073 14

certified_graph_case record002 29 22997545058304 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11692 14

certified_graph_case record003 29 23006130798592 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11693 14

certified_graph_case record004 29 23006799724544 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11694 14

theorem record005_parameters : Parameters record005 (rowOfCode 29) 23014724861952 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 23014724861952 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11695 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 23014724861952
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch116.candidate11695_checked

theorem record005_result : Result (29, 23014724861952) :=
  of_direct_small 29 23014724861952 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00134.record005.direct_core, record005_parameters, record005_coverage⟩
#print axioms record005_result

certified_graph_case record006 29 23108580810816 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11696 14

certified_graph_case record007 29 23168799539456 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15074 14

certified_graph_case record008 29 23177121038592 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15075 14

certified_graph_case record009 29 23177389441280 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15076 14

certified_graph_case record010 29 23177400950784 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11697 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00134

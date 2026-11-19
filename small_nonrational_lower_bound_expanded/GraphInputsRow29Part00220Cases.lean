module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00220Checked
public import GraphInputsRow29Part00220Metadata
public import GraphInputsRow29Part00220Frames
public import GraphInputsRow29Part00220Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch120
public import GraphCoverageBatch154
public import GraphInputsRow29Part00220Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00220
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 29766674087936 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15442 14

theorem record001_parameters : Parameters record001 (rowOfCode 29) 29772914888832 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29772914888832 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12036 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 29772914888832
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch120.candidate12036_checked

theorem record001_result : Result (29, 29772914888832) :=
  of_direct_small 29 29772914888832 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00220.record001.direct_core, record001_parameters, record001_coverage⟩

certified_graph_case record002 29 29773988364928 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15443 14

certified_graph_case record003 29 29831098597376 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15444 14

certified_graph_case record004 29 29833985802496 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15445 14

certified_graph_case record005 29 29834120069120 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15446 14

certified_graph_case record006 29 29835025989888 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15447 14

certified_graph_case record007 29 29837172424960 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15448 14

certified_graph_case record008 29 29902705328128 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12037 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00220

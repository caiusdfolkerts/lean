module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00254Checked
public import GraphInputsRow29Part00254Metadata
public import GraphInputsRow29Part00254Frames
public import GraphInputsRow29Part00254Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch122
public import GraphCoverageBatch155
public import GraphInputsRow29Part00254Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00254
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 32505457606912 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15524 14

certified_graph_case record001 29 32514051735552 GraphCoverageDescriptions.GraphCoverageBatch122.candidate12210 14

certified_graph_case record002 29 32514588540928 GraphCoverageDescriptions.GraphCoverageBatch122.candidate12211 14

certified_graph_case record003 29 32515091922944 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15525 14

theorem record004_parameters : Parameters record004 (rowOfCode 29) 32522637475840 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32522637475840 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch122.candidate12212 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 32522637475840
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch122.candidate12212_checked

theorem record004_result : Result (29, 32522637475840) :=
  of_direct_small 29 32522637475840 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00254.record004.direct_core, record004_parameters, record004_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00254

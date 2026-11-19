module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00246Checked
public import GraphInputsRow29Part00246Metadata
public import GraphInputsRow29Part00246Frames
public import GraphInputsRow29Part00246Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch121
public import GraphCoverageBatch155
public import GraphInputsRow29Part00246Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00246
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 29) 31938788261888 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31938788261888 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12180 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 31938788261888
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch121.candidate12180_checked

theorem record000_result : Result (29, 31938788261888) :=
  of_direct_small 29 31938788261888 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00246.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 29 31939559981312 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15515 14

certified_graph_case record002 29 31940330143744 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12181 14

certified_graph_case record003 29 31960731811840 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15516 14

theorem record004_parameters : Parameters record004 (rowOfCode 29) 31963709186048 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31963709186048 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12182 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 31963709186048
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch121.candidate12182_checked

theorem record004_result : Result (29, 31963709186048) :=
  of_direct_small 29 31963709186048 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00246.record004.direct_core, record004_parameters, record004_coverage⟩

certified_graph_case record005 29 31972294926336 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12183 14

theorem record006_parameters : Parameters record006 (rowOfCode 29) 31973615600160 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31973615600160 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12184 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 31973615600160
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch121.candidate12184_checked

theorem record006_result : Result (29, 31973615600160) :=
  of_direct_small 29 31973615600160 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00246.record006.direct_core, record006_parameters, record006_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00246

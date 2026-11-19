module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00096Checked
public import GraphInputsRow29Part00096Metadata
public import GraphInputsRow29Part00096Frames
public import GraphInputsRow29Part00096Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch114
public import GraphCoverageBatch147
public import GraphInputsRow29Part00096Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00096
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 16711793311744 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14772 14

certified_graph_case record001 29 16720379052032 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11422 14

certified_graph_case record002 29 16721114038272 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11423 14

theorem record003_parameters : Parameters record003 (rowOfCode 29) 16769851359488 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 16769851359488 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11424 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 16769851359488
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch114.candidate11424_checked

theorem record003_result : Result (29, 16769851359488) :=
  of_direct_small 29 16769851359488 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00096.record003.direct_core, record003_parameters, record003_coverage⟩

theorem record004_parameters : Parameters record004 (rowOfCode 29) 16769863389184 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 16769863389184 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11425 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 16769863389184
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch114.candidate11425_checked

theorem record004_result : Result (29, 16769863389184) :=
  of_direct_small 29 16769863389184 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00096.record004.direct_core, record004_parameters, record004_coverage⟩

certified_graph_case record005 29 16769995509760 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11426 14

theorem record006_parameters : Parameters record006 (rowOfCode 29) 16770253996160 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 16770253996160 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11427 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 16770253996160
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch114.candidate11427_checked

theorem record006_result : Result (29, 16770253996160) :=
  of_direct_small 29 16770253996160 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00096.record006.direct_core, record006_parameters, record006_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00096

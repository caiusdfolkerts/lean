module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00029Checked
public import GraphInputsRow31Part00029Metadata
public import GraphInputsRow31Part00029Frames
public import GraphInputsRow31Part00029Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch158
public import GraphInputsRow31Part00029Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00029
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 31) 6857053765632 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 6857053765632 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15865 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 6857053765632
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch158.candidate15865_checked

theorem record000_result : Result (31, 6857053765632) :=
  of_direct_small 31 6857053765632 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00029.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 31 6885235761408 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15866 14

theorem record002_parameters : Parameters record002 (rowOfCode 31) 6890610237440 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 6890610237440 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15867 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 6890610237440
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch158.candidate15867_checked

theorem record002_result : Result (31, 6890610237440) :=
  of_direct_small 31 6890610237440 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00029.record002.direct_core, record002_parameters, record002_coverage⟩

certified_graph_case record003 31 6898523316288 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15868 14

certified_graph_case record004 31 6919594967808 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15869 14

certified_graph_case record005 31 6919875985408 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15870 14

certified_graph_case record006 31 6928587555456 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15871 14

certified_graph_case record007 31 6932882522688 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15872 14

certified_graph_case record008 31 6962948374528 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15873 14

theorem record009_parameters : Parameters record009 (rowOfCode 31) 6986175348736 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 6986175348736 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15874 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 6986175348736
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.small_allowed record009 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch158.candidate15874_checked

theorem record009_result : Result (31, 6986175348736) :=
  of_direct_small 31 6986175348736 (by decide) ⟨record009, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00029.record009.direct_core, record009_parameters, record009_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00029

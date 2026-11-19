module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00196Checked
public import GraphInputsRow29Part00196Metadata
public import GraphInputsRow29Part00196Frames
public import GraphInputsRow29Part00196Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch119
public import GraphCoverageBatch153
public import GraphInputsRow29Part00196Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00196
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 29) 28627244711936 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 28627244711936 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11944 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 28627244711936
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch119.candidate11944_checked

theorem record000_result : Result (29, 28627244711936) :=
  of_direct_small 29 28627244711936 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00196.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 29 28627368444160 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15378 14

certified_graph_case record002 29 28627372670976 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15379 14

certified_graph_case record003 29 28627376832512 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15380 14

theorem record004_parameters : Parameters record004 (rowOfCode 29) 28627636879488 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 28627636879488 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15381 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 28627636879488
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch153.candidate15381_checked

theorem record004_result : Result (29, 28627636879488) :=
  of_direct_small 29 28627636879488 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00196.record004.direct_core, record004_parameters, record004_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00196

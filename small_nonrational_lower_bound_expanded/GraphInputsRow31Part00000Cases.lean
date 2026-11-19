module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00000Checked
public import GraphInputsRow31Part00000Metadata
public import GraphInputsRow31Part00000Frames
public import GraphInputsRow31Part00000Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch155
public import GraphInputsRow31Part00000Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00000
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 3328262528 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15569 14

theorem record001_parameters : Parameters record001 (rowOfCode 31) 3394322816 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 3394322816 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15570 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 3394322816
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch155.candidate15570_checked

theorem record001_result : Result (31, 3394322816) :=
  of_direct_small 31 3394322816 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00000.record001.direct_core, record001_parameters, record001_coverage⟩

certified_graph_case record002 31 37994201344 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15571 14

theorem record003_parameters : Parameters record003 (rowOfCode 31) 38262636672 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 38262636672 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15572 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 38262636672
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch155.candidate15572_checked

theorem record003_result : Result (31, 38262636672) :=
  of_direct_small 31 38262636672 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00000.record003.direct_core, record003_parameters, record003_coverage⟩

certified_graph_case record004 31 39934034816 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15573 14

certified_graph_case record005 31 40074576128 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15574 14

theorem record006_parameters : Parameters record006 (rowOfCode 31) 40343011456 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 40343011456 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15575 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 40343011456
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch155.candidate15575_checked

theorem record006_result : Result (31, 40343011456) :=
  of_direct_small 31 40343011456 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00000.record006.direct_core, record006_parameters, record006_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00000

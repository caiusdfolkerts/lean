module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00059Checked
public import GraphInputsRow29Part00059Metadata
public import GraphInputsRow29Part00059Frames
public import GraphInputsRow29Part00059Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch111
public import GraphCoverageBatch145
public import GraphInputsRow29Part00059Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00059
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 11040622383360 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11106 14

certified_graph_case record001 29 11070022361216 GraphCoverageDescriptions.GraphCoverageBatch145.candidate14570 14

certified_graph_case record002 29 11074183110784 GraphCoverageDescriptions.GraphCoverageBatch145.candidate14571 14

certified_graph_case record003 29 11082504609920 GraphCoverageDescriptions.GraphCoverageBatch145.candidate14572 14

certified_graph_case record004 29 11109616615424 GraphCoverageDescriptions.GraphCoverageBatch145.candidate14573 14

certified_graph_case record005 29 11118330282112 GraphCoverageDescriptions.GraphCoverageBatch145.candidate14574 14

theorem record006_parameters : Parameters record006 (rowOfCode 29) 11189196177536 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 11189196177536 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch145.candidate14575 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 11189196177536
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch145.candidate14575_checked

theorem record006_result : Result (29, 11189196177536) :=
  of_direct_small 29 11189196177536 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00059.record006.direct_core, record006_parameters, record006_coverage⟩

certified_graph_case record007 29 11238073499648 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11107 14

certified_graph_case record008 29 11242894786560 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11108 14

certified_graph_case record009 29 11246774518528 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11109 14

theorem record010_parameters : Parameters record010 (rowOfCode 29) 11247055536128 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record010_coverage : Coverage record010 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 11247055536128 :=
  GraphCoverageDescriptions.coverage_of_checked record010 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11110 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 11247055536128
    (by rfl) record010_cells_exact
    (GraphCoverageDescriptions.small_allowed record010 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch111.candidate11110_checked

theorem record010_result : Result (29, 11247055536128) :=
  of_direct_small 29 11247055536128 (by decide) ⟨record010, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00059.record010.direct_core, record010_parameters, record010_coverage⟩

theorem record011_parameters : Parameters record011 (rowOfCode 29) 11255769235456 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record011_coverage : Coverage record011 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 11255769235456 :=
  GraphCoverageDescriptions.coverage_of_checked record011 GraphCoverageDescriptions.GraphCoverageBatch145.candidate14576 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 11255769235456
    (by rfl) record011_cells_exact
    (GraphCoverageDescriptions.small_allowed record011 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch145.candidate14576_checked

theorem record011_result : Result (29, 11255769235456) :=
  of_direct_small 29 11255769235456 (by decide) ⟨record011, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00059.record011.direct_core, record011_parameters, record011_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00059

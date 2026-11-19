module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00084Checked
public import GraphInputsRow29Part00084Metadata
public import GraphInputsRow29Part00084Frames
public import GraphInputsRow29Part00084Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch113
public import GraphCoverageBatch146
public import GraphInputsRow29Part00084Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00084
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 13900394299648 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11331 14

certified_graph_case record001 29 13900405809152 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11332 14

certified_graph_case record002 29 13907909943552 GraphCoverageDescriptions.GraphCoverageBatch146.candidate14689 14

certified_graph_case record003 29 13929392701440 GraphCoverageDescriptions.GraphCoverageBatch146.candidate14690 14

certified_graph_case record004 29 13933440139265 GraphCoverageDescriptions.GraphCoverageBatch146.candidate14691 14

certified_graph_case record005 29 13937978441728 GraphCoverageDescriptions.GraphCoverageBatch146.candidate14692 14

certified_graph_case record006 29 13937986764800 GraphCoverageDescriptions.GraphCoverageBatch146.candidate14693 14

certified_graph_case record007 29 13975894950144 GraphCoverageDescriptions.GraphCoverageBatch146.candidate14694 14

certified_graph_case record008 29 13976630001664 GraphCoverageDescriptions.GraphCoverageBatch146.candidate14695 14

theorem record009_parameters : Parameters record009 (rowOfCode 29) 14027929423904 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 14027929423904 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11333 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 14027929423904
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.small_allowed record009 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch113.candidate11333_checked

theorem record009_result : Result (29, 14027929423904) :=
  of_direct_small 29 14027929423904 (by decide) ⟨record009, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00084.record009.direct_core, record009_parameters, record009_coverage⟩

theorem record010_parameters : Parameters record010 (rowOfCode 29) 14294884909088 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record010_coverage : Coverage record010 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 14294884909088 :=
  GraphCoverageDescriptions.coverage_of_checked record010 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11334 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 14294884909088
    (by rfl) record010_cells_exact
    (GraphCoverageDescriptions.small_allowed record010 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch113.candidate11334_checked

theorem record010_result : Result (29, 14294884909088) :=
  of_direct_small 29 14294884909088 (by decide) ⟨record010, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00084.record010.direct_core, record010_parameters, record010_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00084

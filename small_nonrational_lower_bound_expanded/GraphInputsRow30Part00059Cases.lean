module
prelude
public meta import GraphCases
public import GraphInputsRow30Part00059Checked
public import GraphInputsRow30Part00059Metadata
public import GraphInputsRow30Part00059Frames
public import GraphInputsRow30Part00059Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch123
public import GraphInputsRow30Part00059Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00059
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 30 34737716527104 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12353 14

certified_graph_case record001 30 34739046055936 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12354 14

certified_graph_case record002 30 34763465424896 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12356 14

certified_graph_case record003 30 34763498848256 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12357 14

certified_graph_case record004 30 34789235230736 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12358 14

certified_graph_case record005 30 34790308839940 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12359 14

certified_graph_case record006 30 34840774838528 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12360 14

certified_graph_case record007 30 34875159609344 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12361 14

certified_graph_case record008 30 34892331089920 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12362 14

certified_graph_case record009 30 35115652745216 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12363 14

theorem record010_parameters : Parameters record010 (rowOfCode 30) 35115669651456 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record010_coverage : Coverage record010 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 35115669651456 :=
  GraphCoverageDescriptions.coverage_of_checked record010 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12364 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 35115669651456
    (by rfl) record010_cells_exact
    (GraphCoverageDescriptions.small_allowed record010 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch123.candidate12364_checked

theorem record010_result : Result (30, 35115669651456) :=
  of_direct_small 30 35115669651456 (by decide) ⟨record010, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00059.record010.direct_core, record010_parameters, record010_coverage⟩

certified_graph_case record011 30 35150029127680 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12365 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00059

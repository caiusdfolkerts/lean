module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00021Checked
public import GraphInputsRow29Part00021Metadata
public import GraphInputsRow29Part00021Frames
public import GraphInputsRow29Part00021Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch107
public import GraphCoverageBatch143
public import GraphInputsRow29Part00021Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00021
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 5026529477376 GraphCoverageDescriptions.GraphCoverageBatch143.candidate14384 14

certified_graph_case record001 29 5026730967072 GraphCoverageDescriptions.GraphCoverageBatch143.candidate14385 14

certified_graph_case record002 29 5089830445312 GraphCoverageDescriptions.GraphCoverageBatch107.candidate10769 14

certified_graph_case record003 29 5104109453312 GraphCoverageDescriptions.GraphCoverageBatch107.candidate10770 14

certified_graph_case record004 29 5104178569472 GraphCoverageDescriptions.GraphCoverageBatch143.candidate14386 14

certified_graph_case record005 29 5123505979392 GraphCoverageDescriptions.GraphCoverageBatch107.candidate10771 14

certified_graph_case record006 29 5137345118208 GraphCoverageDescriptions.GraphCoverageBatch143.candidate14387 14

certified_graph_case record007 29 5138460737792 GraphCoverageDescriptions.GraphCoverageBatch107.candidate10772 14

certified_graph_case record008 29 5140140589312 GraphCoverageDescriptions.GraphCoverageBatch143.candidate14388 14

certified_graph_case record009 29 5140413218816 GraphCoverageDescriptions.GraphCoverageBatch143.candidate14389 14

certified_graph_case record010 29 5140677459968 GraphCoverageDescriptions.GraphCoverageBatch107.candidate10773 14

certified_graph_case record011 29 5140685783040 GraphCoverageDescriptions.GraphCoverageBatch107.candidate10774 14

theorem record012_parameters : Parameters record012 (rowOfCode 29) 5140950024192 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record012_coverage : Coverage record012 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 5140950024192 :=
  GraphCoverageDescriptions.coverage_of_checked record012 GraphCoverageDescriptions.GraphCoverageBatch107.candidate10775 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 5140950024192
    (by rfl) record012_cells_exact
    (GraphCoverageDescriptions.small_allowed record012 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch107.candidate10775_checked

theorem record012_result : Result (29, 5140950024192) :=
  of_direct_small 29 5140950024192 (by decide) ⟨record012, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00021.record012.direct_core, record012_parameters, record012_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00021

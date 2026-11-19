module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00232Checked
public import GraphInputsRow29Part00232Metadata
public import GraphInputsRow29Part00232Frames
public import GraphInputsRow29Part00232Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch121
public import GraphCoverageBatch154
public import GraphInputsRow29Part00232Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00232
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 30942364180480 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15482 14

certified_graph_case record001 29 30942421852416 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15483 14

certified_graph_case record002 29 30942824505408 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12125 14

certified_graph_case record003 29 30943495069952 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15484 14

certified_graph_case record004 29 30943897722944 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12126 14

certified_graph_case record005 29 30946045206560 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12127 14

certified_graph_case record006 29 30969467830272 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12128 14

certified_graph_case record007 29 30969532777216 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15485 14

certified_graph_case record008 29 30977854276352 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15486 14

certified_graph_case record009 29 30978256929344 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12129 14

certified_graph_case record010 29 30980404412960 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12130 14

certified_graph_case record011 29 31014027034880 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15487 14

certified_graph_case record012 29 31014765207552 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12131 14

certified_graph_case record013 29 31063514550304 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15488 14

certified_graph_case record014 29 31063910912032 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12132 14

theorem record015_parameters : Parameters record015 (rowOfCode 29) 31065793105952 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record015_coverage : Coverage record015 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31065793105952 :=
  GraphCoverageDescriptions.coverage_of_checked record015 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12133 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 31065793105952
    (by rfl) record015_cells_exact
    (GraphCoverageDescriptions.small_allowed record015 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch121.candidate12133_checked

theorem record015_result : Result (29, 31065793105952) :=
  of_direct_small 29 31065793105952 (by decide) ⟨record015, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00232.record015.direct_core, record015_parameters, record015_coverage⟩
#print axioms record015_result

certified_graph_case record016 29 31065842651168 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12134 14

certified_graph_case record017 29 31072344088832 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15489 14

certified_graph_case record018 29 31099390558208 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12135 14

certified_graph_case record019 29 31244345671680 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12136 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00232

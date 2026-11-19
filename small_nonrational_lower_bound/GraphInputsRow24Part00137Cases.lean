module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00137Checked
public import GraphInputsRow24Part00137Metadata
public import GraphInputsRow24Part00137Frames
public import GraphInputsRow24Part00137Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch100
public import GraphInputsRow24Part00137Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00137
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 31751825063936 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10079 14

certified_graph_case record001 24 31751833387008 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10080 14

certified_graph_case record002 24 31752023244800 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10081 14

certified_graph_case record003 24 31753835151616 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10082 14

theorem record004_parameters : Parameters record004 (rowOfCode 24) 31754103619584 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31754103619584 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10083 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 31754103619584
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch100.candidate10083_checked

theorem record004_result : Result (24, 31754103619584) :=
  of_direct_small 24 31754103619584 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00137.record004.direct_core, record004_parameters, record004_coverage⟩
#print axioms record004_result

certified_graph_case record005 24 31754111942656 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10084 14

certified_graph_case record006 24 31754573324288 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10085 14

certified_graph_case record007 24 31754875339008 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10086 14

certified_graph_case record008 24 31755646541824 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10087 14

certified_graph_case record009 24 31758264369152 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10088 14

certified_graph_case record010 24 31758272692224 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10089 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00137

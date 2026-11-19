module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00038Checked
public import GraphInputsRow24Part00038Metadata
public import GraphInputsRow24Part00038Frames
public import GraphInputsRow24Part00038Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch077
public import GraphInputsRow24Part00038Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 17232893575168 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07761 14

certified_graph_case record001 24 17235703922944 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07762 14

certified_graph_case record002 24 17235741573120 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07763 14

certified_graph_case record003 24 17236509065728 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07764 14

certified_graph_case record004 24 17236509589504 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07765 14

certified_graph_case record005 24 17237054324736 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07766 14

theorem record006_parameters : Parameters record006 (rowOfCode 24) 17244335636480 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 17244335636480 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07767 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 17244335636480
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch077.candidate07767_checked

theorem record006_result : Result (24, 17244335636480) :=
  of_direct_small 24 17244335636480 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00038.record006.direct_core, record006_parameters, record006_coverage⟩
#print axioms record006_result

certified_graph_case record007 24 17244864118784 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07768 14

certified_graph_case record008 24 17282969436416 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07769 14

certified_graph_case record009 24 17291563565056 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07770 14

certified_graph_case record010 24 17292100370432 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07771 14

certified_graph_case record011 24 17300149305344 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07772 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00038

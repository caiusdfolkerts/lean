module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00136Checked
public import GraphInputsRow24Part00136Metadata
public import GraphInputsRow24Part00136Frames
public import GraphInputsRow24Part00136Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch100
public import GraphInputsRow24Part00136Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 24) 31605053849600 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31605053849600 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10070 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 31605053849600
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch100.candidate10070_checked

theorem record000_result : Result (24, 31605053849600) :=
  of_direct_small 24 31605053849600 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00136.record000.direct_core, record000_parameters, record000_coverage⟩
#print axioms record000_result

certified_graph_case record001 24 31622042750976 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10071 14

certified_graph_case record002 24 31622099902720 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10072 14

certified_graph_case record003 24 31655386480640 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10073 14

theorem record004_parameters : Parameters record004 (rowOfCode 24) 31659621613568 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31659621613568 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10074 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 31659621613568
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch100.candidate10074_checked

theorem record004_result : Result (24, 31659621613568) :=
  of_direct_small 24 31659621613568 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00136.record004.direct_core, record004_parameters, record004_coverage⟩
#print axioms record004_result

certified_graph_case record005 24 31689679110144 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10075 14

certified_graph_case record006 24 31722914775040 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10076 14

certified_graph_case record007 24 31722964320256 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10077 14

certified_graph_case record008 24 31751688716544 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10078 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00136

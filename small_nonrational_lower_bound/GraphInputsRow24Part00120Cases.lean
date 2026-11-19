module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00120Checked
public import GraphInputsRow24Part00120Metadata
public import GraphInputsRow24Part00120Frames
public import GraphInputsRow24Part00120Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch097
public import GraphInputsRow24Part00120Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00120
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 24) 28644513693824 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 28644513693824 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch097.candidate09747 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 28644513693824
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch097.candidate09747_checked

theorem record000_result : Result (24, 28644513693824) :=
  of_direct_small 24 28644513693824 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00120.record000.direct_core, record000_parameters, record000_coverage⟩
#print axioms record000_result

certified_graph_case record001 24 28666026279168 GraphCoverageDescriptions.GraphCoverageBatch097.candidate09748 14

certified_graph_case record002 24 28666094428416 GraphCoverageDescriptions.GraphCoverageBatch097.candidate09749 14

certified_graph_case record003 24 28701527965696 GraphCoverageDescriptions.GraphCoverageBatch097.candidate09750 14

certified_graph_case record004 24 28716202737792 GraphCoverageDescriptions.GraphCoverageBatch097.candidate09751 14

theorem record005_parameters : Parameters record005 (rowOfCode 24) 28717292339328 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 28717292339328 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch097.candidate09752 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 28717292339328
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch097.candidate09752_checked

theorem record005_result : Result (24, 28717292339328) :=
  of_direct_small 24 28717292339328 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00120.record005.direct_core, record005_parameters, record005_coverage⟩
#print axioms record005_result

certified_graph_case record006 24 28717294452736 GraphCoverageDescriptions.GraphCoverageBatch097.candidate09753 14

certified_graph_case record007 24 28717298484224 GraphCoverageDescriptions.GraphCoverageBatch097.candidate09754 14

certified_graph_case record008 24 28717426410112 GraphCoverageDescriptions.GraphCoverageBatch097.candidate09755 14

certified_graph_case record009 24 28727048691840 GraphCoverageDescriptions.GraphCoverageBatch097.candidate09756 14

certified_graph_case record010 24 28764811624448 GraphCoverageDescriptions.GraphCoverageBatch097.candidate09757 14

certified_graph_case record011 24 28769168408832 GraphCoverageDescriptions.GraphCoverageBatch097.candidate09758 14

certified_graph_case record012 24 28773397364736 GraphCoverageDescriptions.GraphCoverageBatch097.candidate09759 14

certified_graph_case record013 24 28781718962176 GraphCoverageDescriptions.GraphCoverageBatch097.candidate09760 14

certified_graph_case record014 24 28781850919552 GraphCoverageDescriptions.GraphCoverageBatch097.candidate09761 14

certified_graph_case record015 24 28794627833984 GraphCoverageDescriptions.GraphCoverageBatch097.candidate09762 14

certified_graph_case record016 24 28796163473536 GraphCoverageDescriptions.GraphCoverageBatch097.candidate09763 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00120

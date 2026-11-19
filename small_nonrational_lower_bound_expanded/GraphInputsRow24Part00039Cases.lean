module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00039Checked
public import GraphInputsRow24Part00039Metadata
public import GraphInputsRow24Part00039Frames
public import GraphInputsRow24Part00039Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch077
public import GraphInputsRow24Part00039Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00039
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 17300933836800 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07773 14

certified_graph_case record001 24 17308718399488 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07774 14

certified_graph_case record002 24 17326193774592 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07775 14

certified_graph_case record003 24 17328448798720 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07776 14

certified_graph_case record004 24 17361742594048 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07777 14

certified_graph_case record005 24 17429270888448 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07778 14

certified_graph_case record006 24 17455890071808 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07779 14

theorem record007_parameters : Parameters record007 (rowOfCode 24) 17458106793984 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 17458106793984 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07780 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 17458106793984
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch077.candidate07780_checked

theorem record007_result : Result (24, 17458106793984) :=
  of_direct_small 24 17458106793984 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00039.record007.direct_core, record007_parameters, record007_coverage⟩

theorem record008_parameters : Parameters record008 (rowOfCode 24) 17458379358208 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 17458379358208 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07781 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 17458379358208
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch077.candidate07781_checked

theorem record008_result : Result (24, 17458379358208) :=
  of_direct_small 24 17458379358208 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00039.record008.direct_core, record008_parameters, record008_coverage⟩

certified_graph_case record009 24 17461227356160 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07782 14

certified_graph_case record010 24 17461995372544 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07783 14

certified_graph_case record011 24 17464620482560 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07784 14

certified_graph_case record012 24 17466156122112 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07785 14

certified_graph_case record013 24 17469821419520 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07786 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00039

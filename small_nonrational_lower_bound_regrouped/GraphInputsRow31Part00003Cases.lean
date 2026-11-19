module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00003Checked
public import GraphInputsRow31Part00003Metadata
public import GraphInputsRow31Part00003Frames
public import GraphInputsRow31Part00003Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch155
public import GraphCoverageBatch156
public import GraphInputsRow31Part00003Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00003
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 31) 191943950400 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 191943950400 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15597 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 191943950400
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch155.candidate15597_checked

theorem record000_result : Result (31, 191943950400) :=
  of_direct_small 31 191943950400 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00003.record000.direct_core, record000_parameters, record000_coverage⟩
#print axioms record000_result

certified_graph_case record001 31 194091425856 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15598 14

certified_graph_case record002 31 329246605440 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15599 14

certified_graph_case record003 31 329248686208 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15600 14

certified_graph_case record004 31 550883131776 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15601 14

theorem record005_parameters : Parameters record005 (rowOfCode 31) 550885212544 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 550885212544 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15602 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 550885212544
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch156.candidate15602_checked

theorem record005_result : Result (31, 550885212544) :=
  of_direct_small 31 550885212544 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00003.record005.direct_core, record005_parameters, record005_coverage⟩
#print axioms record005_result

certified_graph_case record006 31 661991227648 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15603 14

certified_graph_case record007 31 661991292928 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15604 14

certified_graph_case record008 31 666529497344 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15605 14

certified_graph_case record009 31 666537885696 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15606 14

certified_graph_case record010 31 679412269312 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15607 14

certified_graph_case record011 31 679422722049 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15608 14

certified_graph_case record012 31 697204539648 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15609 14

certified_graph_case record013 31 697472942336 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15610 14

certified_graph_case record014 31 697473007616 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15611 14

certified_graph_case record015 31 697475023104 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15612 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00003

module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00092Checked
public import GraphInputsRow24Part00092Metadata
public import GraphInputsRow24Part00092Frames
public import GraphInputsRow24Part00092Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch091
public import GraphInputsRow24Part00092Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 25020735193344 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09146 14

certified_graph_case record001 24 25022774120512 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09147 14

certified_graph_case record002 24 25023856263424 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09148 14

certified_graph_case record003 24 25092676452352 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09149 14

certified_graph_case record004 24 25116989917184 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09150 14

certified_graph_case record005 24 25117258481664 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09151 14

theorem record006_parameters : Parameters record006 (rowOfCode 24) 25125827250432 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25125827250432 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09152 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25125827250432
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch091.candidate09152_checked

theorem record006_result : Result (24, 25125827250432) :=
  of_direct_small 24 25125827250432 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record006.direct_core, record006_parameters, record006_coverage⟩
#print axioms record006_result

certified_graph_case record007 24 25125843895040 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09153 14

certified_graph_case record008 24 25125961662464 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09154 14

certified_graph_case record009 24 25128117207040 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09155 14

certified_graph_case record010 24 25152488243456 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09156 14

certified_graph_case record011 24 25152492470272 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09157 14

certified_graph_case record012 24 25152498712576 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09158 14

certified_graph_case record013 24 25152616138752 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09159 14

certified_graph_case record014 24 25152688505088 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09160 14

certified_graph_case record015 24 25152690651136 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09161 14

theorem record016_parameters : Parameters record016 (rowOfCode 24) 25152696893440 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record016_coverage : Coverage record016 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25152696893440 :=
  GraphCoverageDescriptions.coverage_of_checked record016 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09162 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25152696893440
    (by rfl) record016_cells_exact
    (GraphCoverageDescriptions.small_allowed record016 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch091.candidate09162_checked

theorem record016_result : Result (24, 25152696893440) :=
  of_direct_small 24 25152696893440 (by decide) ⟨record016, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00092.record016.direct_core, record016_parameters, record016_coverage⟩
#print axioms record016_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00092

module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00161Checked
public import GraphInputsRow29Part00161Metadata
public import GraphInputsRow29Part00161Frames
public import GraphInputsRow29Part00161Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch118
public import GraphCoverageBatch152
public import GraphInputsRow29Part00161Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 25194833903616 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11800 14

theorem record001_parameters : Parameters record001 (rowOfCode 29) 25194949509120 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25194949509120 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11801 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25194949509120
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch118.candidate11801_checked

theorem record001_result : Result (29, 25194949509120) :=
  of_direct_small 29 25194949509120 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00161.record001.direct_core, record001_parameters, record001_coverage⟩

certified_graph_case record002 29 25198573322240 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15232 14

certified_graph_case record003 29 25211458174976 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15233 14

theorem record004_parameters : Parameters record004 (rowOfCode 29) 25215753125888 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25215753125888 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11802 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25215753125888
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch118.candidate11802_checked

theorem record004_result : Result (29, 25215753125888) :=
  of_direct_small 29 25215753125888 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00161.record004.direct_core, record004_parameters, record004_coverage⟩

certified_graph_case record005 29 25226767237120 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11803 14

certified_graph_case record006 29 25328634364160 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15234 14

certified_graph_case record007 29 25328906993664 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15235 14

certified_graph_case record008 29 25329171234816 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15236 14

certified_graph_case record009 29 25329179557888 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11804 14

certified_graph_case record010 29 25329303355392 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11805 14

certified_graph_case record011 29 25332927234304 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11806 14

certified_graph_case record012 29 25333464104960 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11807 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161

module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00092Checked
public import GraphInputsRow29Part00092Metadata
public import GraphInputsRow29Part00092Frames
public import GraphInputsRow29Part00092Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch113
public import GraphCoverageBatch114
public import GraphCoverageBatch147
public import GraphInputsRow29Part00092Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00092
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 16496472424448 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14742 14

theorem record001_parameters : Parameters record001 (rowOfCode 29) 16496476585984 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 16496476585984 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11395 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 16496476585984
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch113.candidate11395_checked

theorem record001_result : Result (29, 16496476585984) :=
  of_direct_small 29 16496476585984 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00092.record001.direct_core, record001_parameters, record001_coverage⟩

certified_graph_case record002 29 16496567288064 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14743 14

certified_graph_case record003 29 16496579317760 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14744 14

certified_graph_case record004 29 16502952562688 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11396 14

certified_graph_case record005 29 16504083452160 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14745 14

certified_graph_case record006 29 16511274061824 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14746 14

certified_graph_case record007 29 16511499518080 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11397 14

certified_graph_case record008 29 16511501631488 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11398 14

certified_graph_case record009 29 16511532548224 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14747 14

certified_graph_case record010 29 16512673386624 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11399 14

theorem record011_parameters : Parameters record011 (rowOfCode 29) 16527189610752 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record011_coverage : Coverage record011 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 16527189610752 :=
  GraphCoverageDescriptions.coverage_of_checked record011 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11400 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 16527189610752
    (by rfl) record011_cells_exact
    (GraphCoverageDescriptions.small_allowed record011 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch114.candidate11400_checked

theorem record011_result : Result (29, 16527189610752) :=
  of_direct_small 29 16527189610752 (by decide) ⟨record011, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00092.record011.direct_core, record011_parameters, record011_coverage⟩

theorem record012_parameters : Parameters record012 (rowOfCode 29) 16531606079504 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record012_coverage : Coverage record012 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 16531606079504 :=
  GraphCoverageDescriptions.coverage_of_checked record012 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11401 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 16531606079504
    (by rfl) record012_cells_exact
    (GraphCoverageDescriptions.small_allowed record012 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch114.candidate11401_checked

theorem record012_result : Result (29, 16531606079504) :=
  of_direct_small 29 16531606079504 (by decide) ⟨record012, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00092.record012.direct_core, record012_parameters, record012_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00092

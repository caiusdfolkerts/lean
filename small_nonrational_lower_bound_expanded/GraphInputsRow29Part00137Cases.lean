module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00137Checked
public import GraphInputsRow29Part00137Metadata
public import GraphInputsRow29Part00137Frames
public import GraphInputsRow29Part00137Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch117
public import GraphCoverageBatch151
public import GraphInputsRow29Part00137Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00137
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 23555884515328 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11713 14

theorem record001_parameters : Parameters record001 (rowOfCode 29) 23556421320704 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 23556421320704 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11714 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 23556421320704
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch117.candidate11714_checked

theorem record001_result : Result (29, 23556421320704) :=
  of_direct_small 29 23556421320704 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00137.record001.direct_core, record001_parameters, record001_coverage⟩

theorem record002_parameters : Parameters record002 (rowOfCode 29) 23557964890112 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 23557964890112 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11715 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 23557964890112
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch117.candidate11715_checked

theorem record002_result : Result (29, 23557964890112) :=
  of_direct_small 29 23557964890112 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00137.record002.direct_core, record002_parameters, record002_coverage⟩

certified_graph_case record003 29 23590713950208 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11716 14

certified_graph_case record004 29 23679505334528 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15112 14

certified_graph_case record005 29 23680042205184 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15113 14

certified_graph_case record006 29 23683666084096 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15114 14

certified_graph_case record007 29 23684202954752 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15115 14

certified_graph_case record008 29 23686786646272 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15116 14

certified_graph_case record009 29 23692251824384 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15117 14

certified_graph_case record010 29 23692524453888 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15118 14

certified_graph_case record011 29 23692788695040 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15119 14

certified_graph_case record012 29 23692797018112 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11717 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00137

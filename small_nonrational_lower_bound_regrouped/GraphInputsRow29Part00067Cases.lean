module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00067Checked
public import GraphInputsRow29Part00067Metadata
public import GraphInputsRow29Part00067Frames
public import GraphInputsRow29Part00067Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch111
public import GraphCoverageBatch145
public import GraphInputsRow29Part00067Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 12135031668992 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11185 14

certified_graph_case record001 29 12135040057344 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11186 14

certified_graph_case record002 29 12135163789568 GraphCoverageDescriptions.GraphCoverageBatch145.candidate14590 14

certified_graph_case record003 29 12139064524800 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11187 14

certified_graph_case record004 29 12139324539136 GraphCoverageDescriptions.GraphCoverageBatch145.candidate14591 14

certified_graph_case record005 29 12139332927488 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11188 14

certified_graph_case record006 29 12142275789056 GraphCoverageDescriptions.GraphCoverageBatch145.candidate14592 14

theorem record007_parameters : Parameters record007 (rowOfCode 29) 12142544191744 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 12142544191744 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11189 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 12142544191744
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch111.candidate11189_checked

theorem record007_result : Result (29, 12142544191744) :=
  of_direct_small 29 12142544191744 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00067.record007.direct_core, record007_parameters, record007_coverage⟩
#print axioms record007_result

theorem record008_parameters : Parameters record008 (rowOfCode 29) 12142556221440 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 12142556221440 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11190 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 12142556221440
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch111.candidate11190_checked

theorem record008_result : Result (29, 12142556221440) :=
  of_direct_small 29 12142556221440 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00067.record008.direct_core, record008_parameters, record008_coverage⟩
#print axioms record008_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067

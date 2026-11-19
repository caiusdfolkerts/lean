module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00284Checked
public import GraphInputsRow29Part00284Metadata
public import GraphInputsRow29Part00284Frames
public import GraphInputsRow29Part00284Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch123
public import GraphCoverageBatch155
public import GraphInputsRow29Part00284Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00284
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 29) 34535832160256 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34535832160256 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12322 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 34535832160256
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch123.candidate12322_checked

theorem record000_result : Result (29, 34535832160256) :=
  of_direct_small 29 34535832160256 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00284.record000.direct_core, record000_parameters, record000_coverage⟩
#print axioms record000_result

certified_graph_case record001 29 34634666873088 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12323 14

certified_graph_case record002 29 34634667458560 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12324 14

certified_graph_case record003 29 34634675261440 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12325 14

certified_graph_case record004 29 34635170189328 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12326 14

certified_graph_case record005 29 34635707351296 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15533 14

certified_graph_case record006 29 34635725701376 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12327 14

certified_graph_case record007 29 34635744608256 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15534 14

theorem record008_parameters : Parameters record008 (rowOfCode 29) 34635752931328 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34635752931328 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12328 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 34635752931328
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch123.candidate12328_checked

theorem record008_result : Result (29, 34635752931328) :=
  of_direct_small 29 34635752931328 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00284.record008.direct_core, record008_parameters, record008_coverage⟩
#print axioms record008_result

certified_graph_case record009 29 34635759255808 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12329 14

certified_graph_case record010 29 34635975819264 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12330 14

certified_graph_case record011 29 34635984142336 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12331 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00284

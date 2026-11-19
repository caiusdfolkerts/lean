module
prelude
public meta import GraphCases
public import GraphInputsRow23Part00029Checked
public import GraphInputsRow23Part00029Metadata
public import GraphInputsRow23Part00029Frames
public import GraphInputsRow23Part00029Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch059
public import GraphCoverageBatch060
public import GraphInputsRow23Part00029Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 23 32530116968448 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05994 6

certified_graph_case record001 23 32564442234880 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05995 6

certified_graph_case record002 23 32642900754432 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05996 6

certified_graph_case record003 23 32645517934592 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05997 6

theorem record004_parameters : Parameters record004 (rowOfCode 23) 32660080558080 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32660080558080 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05998 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 32660080558080
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch059.candidate05998_checked

theorem record004_result : Result (23, 32660080558080) :=
  of_direct_small 23 32660080558080 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00029.record004.direct_core, record004_parameters, record004_coverage⟩
#print axioms record004_result

certified_graph_case record005 23 32660609040384 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05999 6

certified_graph_case record006 23 32693316222976 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06000 6

certified_graph_case record007 23 32693844705280 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06001 6

certified_graph_case record008 23 32711613907200 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06002 6

certified_graph_case record009 23 32716951191552 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06003 6

certified_graph_case record010 23 32717719207936 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06004 6

certified_graph_case record011 23 32723390496768 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06005 6

certified_graph_case record012 23 32729128239104 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06006 6

theorem record013_parameters : Parameters record013 (rowOfCode 23) 32730201456640 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record013_coverage : Coverage record013 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32730201456640 :=
  GraphCoverageDescriptions.coverage_of_checked record013 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 32730201456640
    (by rfl) record013_cells_exact
    (GraphCoverageDescriptions.small_allowed record013 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch060.candidate06007_checked

theorem record013_result : Result (23, 32730201456640) :=
  of_direct_small 23 32730201456640 (by decide) ⟨record013, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00029.record013.direct_core, record013_parameters, record013_coverage⟩
#print axioms record013_result

certified_graph_case record014 23 32779208261888 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06008 6

certified_graph_case record015 23 32780335513600 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06009 6
end Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00029

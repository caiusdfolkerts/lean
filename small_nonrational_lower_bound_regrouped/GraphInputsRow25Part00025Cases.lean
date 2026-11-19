module
prelude
public meta import GraphCases
public import GraphInputsRow25Part00025Checked
public import GraphInputsRow25Part00025Metadata
public import GraphInputsRow25Part00025Frames
public import GraphInputsRow25Part00025Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch123
public import GraphInputsRow25Part00025Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00025
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 25 34711943053312 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12349 14

certified_graph_case record001 25 34712479858688 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12350 14

certified_graph_case record002 25 34712999624704 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12351 14

certified_graph_case record003 25 34729105690624 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12352 14

certified_graph_case record004 25 34737716527104 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12353 14

certified_graph_case record005 25 34739046055936 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12354 14

certified_graph_case record006 25 34747896037376 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12355 14

certified_graph_case record007 25 34763465424896 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12356 14

certified_graph_case record008 25 34763498848256 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12357 14

certified_graph_case record009 25 34789235230736 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12358 14

certified_graph_case record010 25 34790308839940 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12359 14

certified_graph_case record011 25 34840774838528 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12360 14

certified_graph_case record012 25 34875159609344 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12361 14

certified_graph_case record013 25 34892331089920 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12362 14

certified_graph_case record014 25 35115652745216 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12363 14

theorem record015_parameters : Parameters record015 (rowOfCode 25) 35115669651456 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record015_coverage : Coverage record015 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 35115669651456 :=
  GraphCoverageDescriptions.coverage_of_checked record015 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12364 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 35115669651456
    (by rfl) record015_cells_exact
    (GraphCoverageDescriptions.small_allowed record015 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch123.candidate12364_checked

theorem record015_result : Result (25, 35115669651456) :=
  of_direct_small 25 35115669651456 (by decide) ⟨record015, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00025.record015.direct_core, record015_parameters, record015_coverage⟩
#print axioms record015_result

theorem record016_parameters : Parameters record016 (rowOfCode 25) 35150029127680 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record016_coverage : Coverage record016 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 35150029127680 :=
  GraphCoverageDescriptions.coverage_of_checked record016 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12365 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 35150029127680
    (by rfl) record016_cells_exact
    (GraphCoverageDescriptions.small_allowed record016 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch123.candidate12365_checked

theorem record016_result : Result (25, 35150029127680) :=
  of_direct_small 25 35150029127680 (by decide) ⟨record016, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00025.record016.direct_core, record016_parameters, record016_coverage⟩
#print axioms record016_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00025

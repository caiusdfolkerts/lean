module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00189Checked
public import GraphInputsRow29Part00189Metadata
public import GraphInputsRow29Part00189Frames
public import GraphInputsRow29Part00189Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch119
public import GraphCoverageBatch153
public import GraphInputsRow29Part00189Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00189
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 27404038979712 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15348 14

certified_graph_case record001 29 27493339767040 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15349 14

theorem record002_parameters : Parameters record002 (rowOfCode 29) 27493740322944 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 27493740322944 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15350 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 27493740322944
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch153.candidate15350_checked

theorem record002_result : Result (29, 27493740322944) :=
  of_direct_small 29 27493740322944 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00189.record002.direct_core, record002_parameters, record002_coverage⟩

certified_graph_case record003 29 27561367707776 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15351 14

certified_graph_case record004 29 27562495442945 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15352 14

certified_graph_case record005 29 27566980219136 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15353 14

theorem record006_parameters : Parameters record006 (rowOfCode 29) 27602290999296 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 27602290999296 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11927 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 27602290999296
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch119.candidate11927_checked

theorem record006_result : Result (29, 27602290999296) :=
  of_direct_small 29 27602290999296 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00189.record006.direct_core, record006_parameters, record006_coverage⟩

theorem record007_parameters : Parameters record007 (rowOfCode 29) 27602414796800 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 27602414796800 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15354 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 27602414796800
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch153.candidate15354_checked

theorem record007_result : Result (29, 27602414796800) :=
  of_direct_small 29 27602414796800 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00189.record007.direct_core, record007_parameters, record007_coverage⟩

certified_graph_case record008 29 27635565478144 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15355 14

certified_graph_case record009 29 27638786171136 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15356 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00189

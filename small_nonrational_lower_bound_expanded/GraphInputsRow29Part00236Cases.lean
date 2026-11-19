module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00236Checked
public import GraphInputsRow29Part00236Metadata
public import GraphInputsRow29Part00236Frames
public import GraphInputsRow29Part00236Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch121
public import GraphCoverageBatch154
public import GraphInputsRow29Part00236Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00236
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 29) 31431376510976 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31431376510976 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12146 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 31431376510976
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch121.candidate12146_checked

theorem record000_result : Result (29, 31431376510976) :=
  of_direct_small 29 31431376510976 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00236.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 29 31441580785920 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15493 14

certified_graph_case record002 29 31448308449280 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15494 14

certified_graph_case record003 29 31448316772352 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12147 14

certified_graph_case record004 29 31450174914560 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15495 14

theorem record005_parameters : Parameters record005 (rowOfCode 29) 31450711719936 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31450711719936 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12148 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 31450711719936
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch121.candidate12148_checked

theorem record005_result : Result (29, 31450711719936) :=
  of_direct_small 29 31450711719936 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00236.record005.direct_core, record005_parameters, record005_coverage⟩

certified_graph_case record006 29 31465001779200 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12149 14

theorem record007_parameters : Parameters record007 (rowOfCode 29) 31465736765440 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31465736765440 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12150 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 31465736765440
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch121.candidate12150_checked

theorem record007_result : Result (29, 31465736765440) :=
  of_direct_small 29 31465736765440 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00236.record007.direct_core, record007_parameters, record007_coverage⟩

certified_graph_case record008 29 31474082648096 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12151 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00236

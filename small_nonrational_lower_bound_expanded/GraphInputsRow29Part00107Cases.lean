module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00107Checked
public import GraphInputsRow29Part00107Metadata
public import GraphInputsRow29Part00107Frames
public import GraphInputsRow29Part00107Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch115
public import GraphCoverageBatch148
public import GraphInputsRow29Part00107Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00107
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 18406359236608 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14856 14

theorem record001_parameters : Parameters record001 (rowOfCode 29) 18406359302144 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 18406359302144 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11551 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 18406359302144
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch115.candidate11551_checked

theorem record001_result : Result (29, 18406359302144) :=
  of_direct_small 29 18406359302144 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00107.record001.direct_core, record001_parameters, record001_coverage⟩

certified_graph_case record002 29 18406887653888 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11552 14

theorem record003_parameters : Parameters record003 (rowOfCode 29) 18406896041984 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 18406896041984 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11553 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 18406896041984
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch115.candidate11553_checked

theorem record003_result : Result (29, 18406896041984) :=
  of_direct_small 29 18406896041984 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00107.record003.direct_core, record003_parameters, record003_coverage⟩

certified_graph_case record004 29 18435486523520 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14857 14

certified_graph_case record005 29 18471180075136 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14858 14

theorem record006_parameters : Parameters record006 (rowOfCode 29) 18522338033664 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 18522338033664 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11554 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 18522338033664
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch115.candidate11554_checked

theorem record006_result : Result (29, 18522338033664) :=
  of_direct_small 29 18522338033664 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00107.record006.direct_core, record006_parameters, record006_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00107

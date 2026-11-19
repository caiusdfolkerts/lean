module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00039Checked
public import GraphInputsRow29Part00039Metadata
public import GraphInputsRow29Part00039Frames
public import GraphInputsRow29Part00039Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch109
public import GraphCoverageBatch144
public import GraphInputsRow29Part00039Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00039
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 7562766320384 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10933 14

certified_graph_case record001 29 7563039014912 GraphCoverageDescriptions.GraphCoverageBatch144.candidate14449 14

certified_graph_case record002 29 7563047337984 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10934 14

theorem record003_parameters : Parameters record003 (rowOfCode 29) 7564846695168 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 7564846695168 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10935 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 7564846695168
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch109.candidate10935_checked

theorem record003_result : Result (29, 7564846695168) :=
  of_direct_small 29 7564846695168 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00039.record003.direct_core, record003_parameters, record003_coverage⟩

certified_graph_case record004 29 7564855148544 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10936 14

certified_graph_case record005 29 7565119389696 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10937 14

theorem record006_parameters : Parameters record006 (rowOfCode 29) 7565127712768 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 7565127712768 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10938 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 7565127712768
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch109.candidate10938_checked

theorem record006_result : Result (29, 7565127712768) :=
  of_direct_small 29 7565127712768 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00039.record006.direct_core, record006_parameters, record006_coverage⟩

theorem record007_parameters : Parameters record007 (rowOfCode 29) 7572607205376 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 7572607205376 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10939 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 7572607205376
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch109.candidate10939_checked

theorem record007_result : Result (29, 7572607205376) :=
  of_direct_small 29 7572607205376 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00039.record007.direct_core, record007_parameters, record007_coverage⟩

certified_graph_case record008 29 7577465291008 GraphCoverageDescriptions.GraphCoverageBatch144.candidate14450 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00039

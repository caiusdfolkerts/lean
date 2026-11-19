module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00093Checked
public import GraphInputsRow29Part00093Metadata
public import GraphInputsRow29Part00093Frames
public import GraphInputsRow29Part00093Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch114
public import GraphCoverageBatch147
public import GraphInputsRow29Part00093Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00093
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 29) 16531623247873 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 16531623247873 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11402 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 16531623247873
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch114.candidate11402_checked

theorem record000_result : Result (29, 16531623247873) :=
  of_direct_small 29 16531623247873 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00093.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 29 16531623313408 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14748 14

certified_graph_case record002 29 16531883327744 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14749 14

certified_graph_case record003 29 16531891716096 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11403 14

certified_graph_case record004 29 16531895357440 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14750 14

certified_graph_case record005 29 16532675559680 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11404 14

theorem record006_parameters : Parameters record006 (rowOfCode 29) 16532948287488 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 16532948287488 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11405 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 16532948287488
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch114.candidate11405_checked

theorem record006_result : Result (29, 16532948287488) :=
  of_direct_small 29 16532948287488 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00093.record006.direct_core, record006_parameters, record006_coverage⟩

certified_graph_case record007 29 16533212430336 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11406 14

certified_graph_case record008 29 16533220753408 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11407 14

theorem record009_parameters : Parameters record009 (rowOfCode 29) 16536188227584 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 16536188227584 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11408 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 16536188227584
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.small_allowed record009 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch114.candidate11408_checked

theorem record009_result : Result (29, 16536188227584) :=
  of_direct_small 29 16536188227584 (by decide) ⟨record009, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00093.record009.direct_core, record009_parameters, record009_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00093

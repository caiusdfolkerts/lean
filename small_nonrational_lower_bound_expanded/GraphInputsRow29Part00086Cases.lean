module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00086Checked
public import GraphInputsRow29Part00086Metadata
public import GraphInputsRow29Part00086Frames
public import GraphInputsRow29Part00086Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch113
public import GraphCoverageBatch147
public import GraphInputsRow29Part00086Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00086
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 14616457379840 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11350 14

certified_graph_case record001 29 14616579015424 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14709 14

certified_graph_case record002 29 14621748527104 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11351 14

theorem record003_parameters : Parameters record003 (rowOfCode 29) 14623428378624 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 14623428378624 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11352 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 14623428378624
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch113.candidate11352_checked

theorem record003_result : Result (29, 14623428378624) :=
  of_direct_small 29 14623428378624 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00086.record003.direct_core, record003_parameters, record003_coverage⟩

certified_graph_case record004 29 14623700942848 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11353 14

certified_graph_case record005 29 14623965184000 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11354 14

certified_graph_case record006 29 14663823655456 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14710 14

certified_graph_case record007 29 14751207849984 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14711 14

theorem record008_parameters : Parameters record008 (rowOfCode 29) 14759793590272 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 14759793590272 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11355 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 14759793590272
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch113.candidate11355_checked

theorem record008_result : Result (29, 14759793590272) :=
  of_direct_small 29 14759793590272 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00086.record008.direct_core, record008_parameters, record008_coverage⟩

certified_graph_case record009 29 14760462516224 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11356 14

theorem record010_parameters : Parameters record010 (rowOfCode 29) 14768387653632 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record010_coverage : Coverage record010 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 14768387653632 :=
  GraphCoverageDescriptions.coverage_of_checked record010 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11357 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 14768387653632
    (by rfl) record010_cells_exact
    (GraphCoverageDescriptions.small_allowed record010 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch113.candidate11357_checked

theorem record010_result : Result (29, 14768387653632) :=
  of_direct_small 29 14768387653632 (by decide) ⟨record010, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00086.record010.direct_core, record010_parameters, record010_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00086

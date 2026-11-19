module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00237Checked
public import GraphInputsRow29Part00237Metadata
public import GraphInputsRow29Part00237Frames
public import GraphInputsRow29Part00237Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch121
public import GraphCoverageBatch154
public import GraphCoverageBatch155
public import GraphInputsRow29Part00237Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00237
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 31482664460544 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15496 14

certified_graph_case record001 29 31482672848896 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15497 14

certified_graph_case record002 29 31483729420288 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15498 14

certified_graph_case record003 29 31483788002048 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15499 14

certified_graph_case record004 29 31491505786912 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12152 14

certified_graph_case record005 29 31491843195136 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15500 14

certified_graph_case record006 29 31492109501184 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15501 14

certified_graph_case record007 29 31492177723392 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15502 14

theorem record008_parameters : Parameters record008 (rowOfCode 29) 31492579263008 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31492579263008 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12153 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 31492579263008
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch121.candidate12153_checked

theorem record008_result : Result (29, 31492579263008) :=
  of_direct_small 29 31492579263008 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00237.record008.direct_core, record008_parameters, record008_coverage⟩

certified_graph_case record009 29 31495029817600 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15503 14

theorem record010_parameters : Parameters record010 (rowOfCode 29) 31495801020416 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record010_coverage : Coverage record010 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31495801020416 :=
  GraphCoverageDescriptions.coverage_of_checked record010 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12154 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 31495801020416
    (by rfl) record010_cells_exact
    (GraphCoverageDescriptions.small_allowed record010 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch121.candidate12154_checked

theorem record010_result : Result (29, 31495801020416) :=
  of_direct_small 29 31495801020416 (by decide) ⟨record010, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00237.record010.direct_core, record010_parameters, record010_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00237

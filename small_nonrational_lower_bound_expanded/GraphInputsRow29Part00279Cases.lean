module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00279Checked
public import GraphInputsRow29Part00279Metadata
public import GraphInputsRow29Part00279Frames
public import GraphInputsRow29Part00279Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch123
public import GraphInputsRow29Part00279Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00279
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 34159020015616 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12302 14

certified_graph_case record001 29 34160060203008 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12303 14

certified_graph_case record002 29 34213709480452 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12304 14

theorem record003_parameters : Parameters record003 (rowOfCode 29) 34224598482944 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34224598482944 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12305 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 34224598482944
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch123.candidate12305_checked

theorem record003_result : Result (29, 34224598482944) :=
  of_direct_small 29 34224598482944 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00279.record003.direct_core, record003_parameters, record003_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00279

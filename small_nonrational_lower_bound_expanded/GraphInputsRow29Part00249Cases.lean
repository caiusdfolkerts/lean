module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00249Checked
public import GraphInputsRow29Part00249Metadata
public import GraphInputsRow29Part00249Frames
public import GraphInputsRow29Part00249Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch121
public import GraphInputsRow29Part00249Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00249
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 32078708080640 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12193 14

theorem record001_parameters : Parameters record001 (rowOfCode 29) 32165295825152 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32165295825152 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12194 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 32165295825152
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch121.candidate12194_checked

theorem record001_result : Result (29, 32165295825152) :=
  of_direct_small 29 32165295825152 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00249.record001.direct_core, record001_parameters, record001_coverage⟩

certified_graph_case record002 29 32169859227712 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12195 14

certified_graph_case record003 29 32172057051136 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12196 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00249

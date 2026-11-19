module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00074Checked
public import GraphInputsRow31Part00074Metadata
public import GraphInputsRow31Part00074Frames
public import GraphInputsRow31Part00074Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch161
public import GraphInputsRow31Part00074Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00074
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 14037098201344 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16184 14

certified_graph_case record001 31 14037635072000 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16185 14

theorem record002_parameters : Parameters record002 (rowOfCode 31) 14037833252864 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 14037833252864 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16186 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 14037833252864
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch161.candidate16186_checked

theorem record002_result : Result (31, 14037833252864) :=
  of_direct_small 31 14037833252864 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00074.record002.direct_core, record002_parameters, record002_coverage⟩

certified_graph_case record003 31 14044577693952 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16187 14

certified_graph_case record004 31 14045348896768 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16188 14

certified_graph_case record005 31 14158632386816 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16189 14

certified_graph_case record006 31 14182053380096 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16190 14

certified_graph_case record007 31 14182788366336 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16191 14

certified_graph_case record008 31 14299322974464 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16192 14

certified_graph_case record009 31 14299591377152 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16193 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00074

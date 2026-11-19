module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00129Checked
public import GraphInputsRow31Part00129Metadata
public import GraphInputsRow31Part00129Frames
public import GraphInputsRow31Part00129Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch166
public import GraphInputsRow31Part00129Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00129
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 31) 29181220028416 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29181220028416 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch166.candidate16672 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 29181220028416
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch166.candidate16672_checked

theorem record000_result : Result (31, 29181220028416) :=
  of_direct_small 31 29181220028416 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00129.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 31 29181492592640 GraphCoverageDescriptions.GraphCoverageBatch166.candidate16673 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00129

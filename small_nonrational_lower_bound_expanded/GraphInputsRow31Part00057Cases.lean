module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00057Checked
public import GraphInputsRow31Part00057Metadata
public import GraphInputsRow31Part00057Frames
public import GraphInputsRow31Part00057Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch160
public import GraphInputsRow31Part00057Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00057
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 31) 12174488043520 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 12174488043520 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16061 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 12174488043520
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch160.candidate16061_checked

theorem record000_result : Result (31, 12174488043520) :=
  of_direct_small 31 12174488043520 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00057.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 31 12211405717504 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16062 14

certified_graph_case record002 31 12219454652416 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16063 14

certified_graph_case record003 31 12219991457792 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16064 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00057

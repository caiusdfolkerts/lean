module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00055Checked
public import GraphInputsRow31Part00055Metadata
public import GraphInputsRow31Part00055Frames
public import GraphInputsRow31Part00055Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch160
public import GraphInputsRow31Part00055Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00055
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 12005238898688 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16056 14

theorem record001_parameters : Parameters record001 (rowOfCode 31) 12013296156672 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 12013296156672 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16057 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 12013296156672
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch160.candidate16057_checked

theorem record001_result : Result (31, 12013296156672) :=
  of_direct_small 31 12013296156672 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00055.record001.direct_core, record001_parameters, record001_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00055

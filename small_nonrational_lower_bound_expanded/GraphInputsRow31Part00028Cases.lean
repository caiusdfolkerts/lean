module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00028Checked
public import GraphInputsRow31Part00028Metadata
public import GraphInputsRow31Part00028Frames
public import GraphInputsRow31Part00028Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch158
public import GraphInputsRow31Part00028Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00028
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 6844844081152 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15863 14

theorem record001_parameters : Parameters record001 (rowOfCode 31) 6851085205504 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 6851085205504 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15864 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 6851085205504
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch158.candidate15864_checked

theorem record001_result : Result (31, 6851085205504) :=
  of_direct_small 31 6851085205504 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00028.record001.direct_core, record001_parameters, record001_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00028

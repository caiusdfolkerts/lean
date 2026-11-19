module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00006Checked
public import GraphInputsRow31Part00006Metadata
public import GraphInputsRow31Part00006Frames
public import GraphInputsRow31Part00006Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch156
public import GraphInputsRow31Part00006Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00006
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 1255814545408 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15641 14

theorem record001_parameters : Parameters record001 (rowOfCode 31) 1255820771392 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 1255820771392 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15642 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 1255820771392
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch156.candidate15642_checked

theorem record001_result : Result (31, 1255820771392) :=
  of_direct_small 31 1255820771392 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00006.record001.direct_core, record001_parameters, record001_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00006

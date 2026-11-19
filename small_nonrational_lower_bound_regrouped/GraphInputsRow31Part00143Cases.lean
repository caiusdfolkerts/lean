module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00143Checked
public import GraphInputsRow31Part00143Metadata
public import GraphInputsRow31Part00143Frames
public import GraphInputsRow31Part00143Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch167
public import GraphInputsRow31Part00143Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00143
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 30323543015424 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16722 14

theorem record001_parameters : Parameters record001 (rowOfCode 31) 30331059179520 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 30331059179520 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16723 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 30331059179520
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch167.candidate16723_checked

theorem record001_result : Result (31, 30331059179520) :=
  of_direct_small 31 30331059179520 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00143.record001.direct_core, record001_parameters, record001_coverage⟩
#print axioms record001_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00143

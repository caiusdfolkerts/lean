module
prelude
public meta import GraphCases
public import GraphInputsRow23Part00037Checked
public import GraphInputsRow23Part00037Metadata
public import GraphInputsRow23Part00037Frames
public import GraphInputsRow23Part00037Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch061
public import GraphInputsRow23Part00037Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00037
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 23) 34892331089920 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34892331089920 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06132 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 34892331089920
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch061.candidate06132_checked

theorem record000_result : Result (23, 34892331089920) :=
  of_direct_small 23 34892331089920 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00037.record000.direct_core, record000_parameters, record000_coverage⟩
#print axioms record000_result

certified_graph_case record001 23 35115652745216 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06133 6

certified_graph_case record002 23 35115669651456 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06134 6

certified_graph_case record003 23 35150029127680 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06135 6
end Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00037

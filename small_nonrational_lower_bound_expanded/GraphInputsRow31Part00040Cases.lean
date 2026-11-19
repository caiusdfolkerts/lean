module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00040Checked
public import GraphInputsRow31Part00040Metadata
public import GraphInputsRow31Part00040Frames
public import GraphInputsRow31Part00040Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch159
public import GraphInputsRow31Part00040Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00040
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 8252016361472 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15939 14

theorem record001_parameters : Parameters record001 (rowOfCode 31) 8252280602624 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8252280602624 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15940 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8252280602624
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch159.candidate15940_checked

theorem record001_result : Result (31, 8252280602624) :=
  of_direct_small 31 8252280602624 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00040.record001.direct_core, record001_parameters, record001_coverage⟩

certified_graph_case record002 31 8252288925696 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15941 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00040

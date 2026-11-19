module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00093Checked
public import GraphInputsRow31Part00093Metadata
public import GraphInputsRow31Part00093Frames
public import GraphInputsRow31Part00093Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch164
public import GraphInputsRow31Part00093Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00093
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 31) 18580834893824 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 18580834893824 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16403 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 18580834893824
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch164.candidate16403_checked

theorem record000_result : Result (31, 18580834893824) :=
  of_direct_small 31 18580834893824 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00093.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 31 18697649397824 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16404 14

certified_graph_case record002 31 18701942267968 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16405 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00093

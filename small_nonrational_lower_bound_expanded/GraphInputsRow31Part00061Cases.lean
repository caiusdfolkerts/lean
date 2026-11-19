module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00061Checked
public import GraphInputsRow31Part00061Metadata
public import GraphInputsRow31Part00061Frames
public import GraphInputsRow31Part00061Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch160
public import GraphInputsRow31Part00061Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00061
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 31) 12792165826560 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 12792165826560 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16088 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 12792165826560
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch160.candidate16088_checked

theorem record000_result : Result (31, 12792165826560) :=
  of_direct_small 31 12792165826560 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00061.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 31 12794707710208 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16089 14

certified_graph_case record002 31 12794749583360 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16090 14

theorem record003_parameters : Parameters record003 (rowOfCode 31) 12800214761472 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 12800214761472 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16091 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 12800214761472
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch160.candidate16091_checked

theorem record003_result : Result (31, 12800214761472) :=
  of_direct_small 31 12800214761472 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00061.record003.direct_core, record003_parameters, record003_coverage⟩

certified_graph_case record004 31 12800487325696 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16092 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00061

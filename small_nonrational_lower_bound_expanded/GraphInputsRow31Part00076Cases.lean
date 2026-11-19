module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00076Checked
public import GraphInputsRow31Part00076Metadata
public import GraphInputsRow31Part00076Frames
public import GraphInputsRow31Part00076Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch161
public import GraphCoverageBatch162
public import GraphInputsRow31Part00076Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00076
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 31) 14371523141632 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 14371523141632 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16197 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 14371523141632
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch161.candidate16197_checked

theorem record000_result : Result (31, 14371523141632) :=
  of_direct_small 31 14371523141632 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00076.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 31 14372646748160 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16198 14

certified_graph_case record002 31 14380108881920 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16199 14

certified_graph_case record003 31 14381429555744 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16200 14

certified_graph_case record004 31 14435939262720 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16201 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00076

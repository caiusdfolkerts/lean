module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00248Checked
public import GraphInputsRow29Part00248Metadata
public import GraphInputsRow29Part00248Frames
public import GraphInputsRow29Part00248Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch121
public import GraphCoverageBatch155
public import GraphInputsRow29Part00248Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00248
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 32042133750336 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15517 14

certified_graph_case record001 29 32042200859168 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15518 14

certified_graph_case record002 29 32043208032256 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12190 14

certified_graph_case record003 29 32060999794688 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15519 14

certified_graph_case record004 29 32075369415232 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15520 14

theorem record005_parameters : Parameters record005 (rowOfCode 29) 32076495585280 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32076495585280 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12191 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 32076495585280
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch121.candidate12191_checked

theorem record005_result : Result (29, 32076495585280) :=
  of_direct_small 29 32076495585280 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00248.record005.direct_core, record005_parameters, record005_coverage⟩

certified_graph_case record006 29 32076963397888 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15521 14

certified_graph_case record007 29 32078179598336 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12192 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00248

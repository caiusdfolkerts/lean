module
prelude
public meta import GraphCases
public import GraphInputsRow26Part00076Checked
public import GraphInputsRow26Part00076Metadata
public import GraphInputsRow26Part00076Frames
public import GraphInputsRow26Part00076Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch102
public import GraphCoverageBatch103
public import GraphInputsRow26Part00076Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00076
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 26 32780558794752 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10295 14

certified_graph_case record001 26 32780600016896 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10296 14

certified_graph_case record002 26 32781069721600 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10297 14

certified_graph_case record003 26 32782411792640 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10298 14

certified_graph_case record004 26 32783216935424 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10299 14

certified_graph_case record005 26 32787797647616 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10300 14

theorem record006_parameters : Parameters record006 (rowOfCode 26) 32787881328640 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32787881328640 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10301 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 32787881328640
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch103.candidate10301_checked

theorem record006_result : Result (26, 32787881328640) :=
  of_direct_small 26 32787881328640 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00076.record006.direct_core, record006_parameters, record006_coverage⟩

certified_graph_case record007 26 32788334518272 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10302 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00076

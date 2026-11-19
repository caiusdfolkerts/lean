module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00151Checked
public import GraphInputsRow31Part00151Metadata
public import GraphInputsRow31Part00151Frames
public import GraphInputsRow31Part00151Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch167
public import GraphInputsRow31Part00151Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00151
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 30839549198336 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16758 14

certified_graph_case record001 31 30839611097088 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16759 14

certified_graph_case record002 31 30842965991424 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16760 14

theorem record003_parameters : Parameters record003 (rowOfCode 31) 30857478283520 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 30857478283520 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16761 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 30857478283520
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch167.candidate16761_checked

theorem record003_result : Result (31, 30857478283520) :=
  of_direct_small 31 30857478283520 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00151.record003.direct_core, record003_parameters, record003_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00151

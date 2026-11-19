module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00138Checked
public import GraphInputsRow31Part00138Metadata
public import GraphInputsRow31Part00138Frames
public import GraphInputsRow31Part00138Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch167
public import GraphInputsRow31Part00138Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00138
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 29811368165376 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16706 14

certified_graph_case record001 31 29871640150016 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16707 14

theorem record002_parameters : Parameters record002 (rowOfCode 31) 30237679190272 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 30237679190272 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16708 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 30237679190272
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch167.candidate16708_checked

theorem record002_result : Result (31, 30237679190272) :=
  of_direct_small 31 30237679190272 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00138.record002.direct_core, record002_parameters, record002_coverage⟩

certified_graph_case record003 31 30241976287232 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16709 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00138

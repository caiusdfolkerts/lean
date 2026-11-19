module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00145Checked
public import GraphInputsRow31Part00145Metadata
public import GraphInputsRow31Part00145Frames
public import GraphInputsRow31Part00145Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch167
public import GraphInputsRow31Part00145Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00145
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 30524332707840 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16729 14

certified_graph_case record001 31 30580167280768 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16730 14

theorem record002_parameters : Parameters record002 (rowOfCode 31) 30717606234112 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 30717606234112 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16731 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 30717606234112
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch167.candidate16731_checked

theorem record002_result : Result (31, 30717606234112) :=
  of_direct_small 31 30717606234112 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00145.record002.direct_core, record002_parameters, record002_coverage⟩
#print axioms record002_result

theorem record003_parameters : Parameters record003 (rowOfCode 31) 30717623140352 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 30717623140352 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16732 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 30717623140352
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch167.candidate16732_checked

theorem record003_result : Result (31, 30717623140352) :=
  of_direct_small 31 30717623140352 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00145.record003.direct_core, record003_parameters, record003_coverage⟩
#print axioms record003_result

certified_graph_case record004 31 30789649596672 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16733 14

certified_graph_case record005 31 30789653823488 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16734 14

certified_graph_case record006 31 30789715656960 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16735 14

certified_graph_case record007 31 30789719883776 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16736 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00145

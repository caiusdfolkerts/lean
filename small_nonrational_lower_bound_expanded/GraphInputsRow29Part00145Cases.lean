module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00145Checked
public import GraphInputsRow29Part00145Metadata
public import GraphInputsRow29Part00145Frames
public import GraphInputsRow29Part00145Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch117
public import GraphCoverageBatch151
public import GraphInputsRow29Part00145Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00145
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 24381189275648 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15170 14

theorem record001_parameters : Parameters record001 (rowOfCode 29) 24414810833152 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24414810833152 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15171 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24414810833152
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch151.candidate15171_checked

theorem record001_result : Result (29, 24414810833152) :=
  of_direct_small 29 24414810833152 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00145.record001.direct_core, record001_parameters, record001_coverage⟩

certified_graph_case record002 29 24417694384672 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15172 14

certified_graph_case record003 29 24436493320192 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15173 14

certified_graph_case record004 29 24437030125568 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11744 14

certified_graph_case record005 29 24441190875136 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15174 14

certified_graph_case record006 29 24443271249920 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15175 14

certified_graph_case record007 29 24449239810048 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15176 14

certified_graph_case record008 29 24449908736000 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11745 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00145

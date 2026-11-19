module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00151Checked
public import GraphInputsRow29Part00151Metadata
public import GraphInputsRow29Part00151Frames
public import GraphInputsRow29Part00151Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch117
public import GraphCoverageBatch151
public import GraphInputsRow29Part00151Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00151
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 24661771436032 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15190 14

theorem record001_parameters : Parameters record001 (rowOfCode 29) 24663986012160 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24663986012160 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11763 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24663986012160
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch117.candidate11763_checked

theorem record001_result : Result (29, 24663986012160) :=
  of_direct_small 29 24663986012160 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00151.record001.direct_core, record001_parameters, record001_coverage⟩
#print axioms record001_result

certified_graph_case record002 29 24666066386944 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11764 14

certified_graph_case record003 29 24666198507520 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11765 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00151

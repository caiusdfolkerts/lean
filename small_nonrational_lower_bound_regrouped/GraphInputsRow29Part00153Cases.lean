module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00153Checked
public import GraphInputsRow29Part00153Metadata
public import GraphInputsRow29Part00153Frames
public import GraphInputsRow29Part00153Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch117
public import GraphCoverageBatch151
public import GraphInputsRow29Part00153Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00153
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 24742413205505 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11771 14

certified_graph_case record001 29 24742813794304 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15192 14

certified_graph_case record002 29 24744960229376 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15193 14

certified_graph_case record003 29 24744984871168 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15194 14

certified_graph_case record004 29 24757838839808 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11772 14

certified_graph_case record005 29 24759010594944 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15195 14

theorem record006_parameters : Parameters record006 (rowOfCode 29) 24777943287824 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24777943287824 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11773 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24777943287824
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch117.candidate11773_checked

theorem record006_result : Result (29, 24777943287824) :=
  of_direct_small 29 24777943287824 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00153.record006.direct_core, record006_parameters, record006_coverage⟩
#print axioms record006_result

certified_graph_case record007 29 24778220536064 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15196 14

certified_graph_case record008 29 24778228924416 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11774 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00153

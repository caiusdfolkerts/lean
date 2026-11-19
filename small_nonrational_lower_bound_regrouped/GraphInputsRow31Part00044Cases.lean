module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00044Checked
public import GraphInputsRow31Part00044Metadata
public import GraphInputsRow31Part00044Frames
public import GraphInputsRow31Part00044Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch159
public import GraphInputsRow31Part00044Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00044
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 8333587185664 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15957 14

certified_graph_case record001 31 8334115602944 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15958 14

certified_graph_case record002 31 8334123991040 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15959 14

certified_graph_case record003 31 8340826624256 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15960 14

certified_graph_case record004 31 8478810701824 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15961 14

certified_graph_case record005 31 8525795885056 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15962 14

theorem record006_parameters : Parameters record006 (rowOfCode 31) 8534100152576 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8534100152576 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15963 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8534100152576
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch159.candidate15963_checked

theorem record006_result : Result (31, 8534100152576) :=
  of_direct_small 31 8534100152576 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00044.record006.direct_core, record006_parameters, record006_coverage⟩
#print axioms record006_result

certified_graph_case record007 31 8538797903872 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15964 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00044

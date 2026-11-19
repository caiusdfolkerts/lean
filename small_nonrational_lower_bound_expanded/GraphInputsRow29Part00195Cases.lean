module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00195Checked
public import GraphInputsRow29Part00195Metadata
public import GraphInputsRow29Part00195Frames
public import GraphInputsRow29Part00195Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch119
public import GraphCoverageBatch153
public import GraphInputsRow29Part00195Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00195
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 28453495635968 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11939 14

certified_graph_case record001 29 28488811675648 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11940 14

certified_graph_case record002 29 28492831981568 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15372 14

theorem record003_parameters : Parameters record003 (rowOfCode 29) 28493484392448 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 28493484392448 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11941 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 28493484392448
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch119.candidate11941_checked

theorem record003_result : Result (29, 28493484392448) :=
  of_direct_small 29 28493484392448 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00195.record003.direct_core, record003_parameters, record003_coverage⟩

certified_graph_case record004 29 28531543244800 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11942 14

certified_graph_case record005 29 28592851394688 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11943 14

certified_graph_case record006 29 28592983515264 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15373 14

certified_graph_case record007 29 28593247756416 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15374 14

certified_graph_case record008 29 28625296457728 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15375 14

certified_graph_case record009 29 28625556504704 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15376 14

certified_graph_case record010 29 28627236323584 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15377 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00195

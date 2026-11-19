module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00244Checked
public import GraphInputsRow29Part00244Metadata
public import GraphInputsRow29Part00244Frames
public import GraphInputsRow29Part00244Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch121
public import GraphCoverageBatch155
public import GraphInputsRow29Part00244Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00244
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 31842955689984 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12175 14

certified_graph_case record001 29 31891509018880 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15512 14

certified_graph_case record002 29 31891777421568 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15513 14

certified_graph_case record003 29 31891788931072 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12176 14

theorem record004_parameters : Parameters record004 (rowOfCode 29) 31896072372480 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31896072372480 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12177 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 31896072372480
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch121.candidate12177_checked

theorem record004_result : Result (29, 31896072372480) :=
  of_direct_small 29 31896072372480 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00244.record004.direct_core, record004_parameters, record004_coverage⟩
#print axioms record004_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00244

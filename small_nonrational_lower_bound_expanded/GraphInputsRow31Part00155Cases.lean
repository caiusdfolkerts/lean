module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00155Checked
public import GraphInputsRow31Part00155Metadata
public import GraphInputsRow31Part00155Frames
public import GraphInputsRow31Part00155Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch167
public import GraphInputsRow31Part00155Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 30915174736128 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16783 14

theorem record001_parameters : Parameters record001 (rowOfCode 31) 30915245965312 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 30915245965312 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16784 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 30915245965312
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch167.candidate16784_checked

theorem record001_result : Result (31, 30915245965312) :=
  of_direct_small 31 30915245965312 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00155.record001.direct_core, record001_parameters, record001_coverage⟩

theorem record002_parameters : Parameters record002 (rowOfCode 31) 30915980951552 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 30915980951552 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16785 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 30915980951552
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch167.candidate16785_checked

theorem record002_result : Result (31, 30915980951552) :=
  of_direct_small 31 30915980951552 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00155.record002.direct_core, record002_parameters, record002_coverage⟩

certified_graph_case record003 31 30969004359680 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16786 14

certified_graph_case record004 31 30969541165056 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16787 14

certified_graph_case record005 31 30977590099968 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16788 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00155

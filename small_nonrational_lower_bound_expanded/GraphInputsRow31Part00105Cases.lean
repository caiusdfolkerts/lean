module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00105Checked
public import GraphInputsRow31Part00105Metadata
public import GraphInputsRow31Part00105Frames
public import GraphInputsRow31Part00105Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch165
public import GraphInputsRow31Part00105Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00105
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 24276901068800 GraphCoverageDescriptions.GraphCoverageBatch165.candidate16506 14

theorem record001_parameters : Parameters record001 (rowOfCode 31) 24298777641216 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24298777641216 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch165.candidate16507 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24298777641216
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch165.candidate16507_checked

theorem record001_result : Result (31, 24298777641216) :=
  of_direct_small 31 24298777641216 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00105.record001.direct_core, record001_parameters, record001_coverage⟩

certified_graph_case record002 31 24299054366720 GraphCoverageDescriptions.GraphCoverageBatch165.candidate16508 14

certified_graph_case record003 31 24312337661952 GraphCoverageDescriptions.GraphCoverageBatch165.candidate16509 14

certified_graph_case record004 31 24345754746880 GraphCoverageDescriptions.GraphCoverageBatch165.candidate16510 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00105

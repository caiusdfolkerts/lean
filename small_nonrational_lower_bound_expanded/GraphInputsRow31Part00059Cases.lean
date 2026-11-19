module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00059Checked
public import GraphInputsRow31Part00059Metadata
public import GraphInputsRow31Part00059Frames
public import GraphInputsRow31Part00059Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch160
public import GraphInputsRow31Part00059Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00059
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 12577950203904 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16073 14

certified_graph_case record001 31 12582383517696 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16074 14

certified_graph_case record002 31 12582912000000 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16075 14

certified_graph_case record003 31 12587072749568 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16076 14

certified_graph_case record004 31 12595130007552 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16077 14

theorem record005_parameters : Parameters record005 (rowOfCode 31) 12654450638848 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 12654450638848 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16078 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 12654450638848
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch160.candidate16078_checked

theorem record005_result : Result (31, 12654450638848) :=
  of_direct_small 31 12654450638848 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00059.record005.direct_core, record005_parameters, record005_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00059

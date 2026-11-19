module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00064Checked
public import GraphInputsRow31Part00064Metadata
public import GraphInputsRow31Part00064Frames
public import GraphInputsRow31Part00064Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch161
public import GraphInputsRow31Part00064Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00064
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 13013751070720 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16106 14

certified_graph_case record001 31 13056719487232 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16107 14

certified_graph_case record002 31 13125441093632 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16108 14

certified_graph_case record003 31 13134035156992 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16109 14

certified_graph_case record004 31 13134563639296 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16110 14

certified_graph_case record005 31 13142620897280 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16111 14

certified_graph_case record006 31 13151189991424 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16112 14

theorem record007_parameters : Parameters record007 (rowOfCode 31) 13234207785216 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 13234207785216 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16113 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 13234207785216
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch161.candidate16113_checked

theorem record007_result : Result (31, 13234207785216) :=
  of_direct_small 31 13234207785216 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00064.record007.direct_core, record007_parameters, record007_coverage⟩

certified_graph_case record008 31 13234216173568 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16114 14

certified_graph_case record009 31 13234674368768 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16115 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00064

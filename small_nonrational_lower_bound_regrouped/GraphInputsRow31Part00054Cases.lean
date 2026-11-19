module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00054Checked
public import GraphInputsRow31Part00054Metadata
public import GraphInputsRow31Part00054Frames
public import GraphInputsRow31Part00054Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch160
public import GraphInputsRow31Part00054Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00054
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 11880017985536 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16048 14

certified_graph_case record001 31 11914239443072 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16049 14

certified_graph_case record002 31 11948871647232 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16050 14

certified_graph_case record003 31 11959474880768 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16051 14

certified_graph_case record004 31 11982958903424 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16052 14

certified_graph_case record005 31 11983027994624 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16053 14

certified_graph_case record006 31 11996116353024 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16054 14

theorem record007_parameters : Parameters record007 (rowOfCode 31) 12004710416384 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 12004710416384 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16055 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 12004710416384
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch160.candidate16055_checked

theorem record007_result : Result (31, 12004710416384) :=
  of_direct_small 31 12004710416384 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00054.record007.direct_core, record007_parameters, record007_coverage⟩
#print axioms record007_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00054

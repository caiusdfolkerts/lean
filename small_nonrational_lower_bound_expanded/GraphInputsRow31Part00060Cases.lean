module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00060Checked
public import GraphInputsRow31Part00060Metadata
public import GraphInputsRow31Part00060Frames
public import GraphInputsRow31Part00060Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch160
public import GraphInputsRow31Part00060Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00060
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 12714449633536 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16079 14

theorem record001_parameters : Parameters record001 (rowOfCode 31) 12721978933248 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 12721978933248 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16080 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 12721978933248
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch160.candidate16080_checked

theorem record001_result : Result (31, 12721978933248) :=
  of_direct_small 31 12721978933248 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00060.record001.direct_core, record001_parameters, record001_coverage⟩

certified_graph_case record002 31 12723043762176 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16081 14

certified_graph_case record003 31 12723580567552 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16082 14

certified_graph_case record004 31 12731629502464 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16083 14

certified_graph_case record005 31 12732166307840 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16084 14

certified_graph_case record006 31 12738910814208 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16085 14

certified_graph_case record007 31 12739678830592 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16086 14

certified_graph_case record008 31 12786403442688 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16087 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00060

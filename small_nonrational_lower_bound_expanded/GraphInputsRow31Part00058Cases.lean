module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00058Checked
public import GraphInputsRow31Part00058Metadata
public import GraphInputsRow31Part00058Frames
public import GraphInputsRow31Part00058Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch160
public import GraphInputsRow31Part00058Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00058
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 12279990976512 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16065 14

theorem record001_parameters : Parameters record001 (rowOfCode 31) 12288039911424 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 12288039911424 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16066 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 12288039911424
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch160.candidate16066_checked

theorem record001_result : Result (31, 12288039911424) :=
  of_direct_small 31 12288039911424 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00058.record001.direct_core, record001_parameters, record001_coverage⟩

theorem record002_parameters : Parameters record002 (rowOfCode 31) 12288576716800 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 12288576716800 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16067 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 12288576716800
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch160.candidate16067_checked

theorem record002_result : Result (31, 12288576716800) :=
  of_direct_small 31 12288576716800 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00058.record002.direct_core, record002_parameters, record002_coverage⟩

certified_graph_case record003 31 12314283606016 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16068 14

certified_graph_case record004 31 12320788971520 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16069 14

certified_graph_case record005 31 12425478832128 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16070 14

theorem record006_parameters : Parameters record006 (rowOfCode 31) 12440511217920 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 12440511217920 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16071 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 12440511217920
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch160.candidate16071_checked

theorem record006_result : Result (31, 12440511217920) :=
  of_direct_small 31 12440511217920 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00058.record006.direct_core, record006_parameters, record006_coverage⟩

certified_graph_case record007 31 12464064331776 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16072 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00058

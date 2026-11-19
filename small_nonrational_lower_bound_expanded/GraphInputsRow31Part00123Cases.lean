module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00123Checked
public import GraphInputsRow31Part00123Metadata
public import GraphInputsRow31Part00123Frames
public import GraphInputsRow31Part00123Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch166
public import GraphInputsRow31Part00123Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00123
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 27266738323456 GraphCoverageDescriptions.GraphCoverageBatch166.candidate16629 14

certified_graph_case record001 31 27307402207360 GraphCoverageDescriptions.GraphCoverageBatch166.candidate16630 14

certified_graph_case record002 31 27404177244160 GraphCoverageDescriptions.GraphCoverageBatch166.candidate16631 14

certified_graph_case record003 31 27562495442944 GraphCoverageDescriptions.GraphCoverageBatch166.candidate16632 14

certified_graph_case record004 31 27575435952128 GraphCoverageDescriptions.GraphCoverageBatch166.candidate16633 14

certified_graph_case record005 31 28041170976768 GraphCoverageDescriptions.GraphCoverageBatch166.candidate16634 14

theorem record006_parameters : Parameters record006 (rowOfCode 31) 28076487016448 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 28076487016448 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch166.candidate16635 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 28076487016448
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch166.candidate16635_checked

theorem record006_result : Result (31, 28076487016448) :=
  of_direct_small 31 28076487016448 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00123.record006.direct_core, record006_parameters, record006_coverage⟩

certified_graph_case record007 31 28076495339520 GraphCoverageDescriptions.GraphCoverageBatch166.candidate16636 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00123

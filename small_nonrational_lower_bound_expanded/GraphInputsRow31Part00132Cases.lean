module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00132Checked
public import GraphInputsRow31Part00132Metadata
public import GraphInputsRow31Part00132Frames
public import GraphInputsRow31Part00132Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch166
public import GraphInputsRow31Part00132Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00132
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 29284370481152 GraphCoverageDescriptions.GraphCoverageBatch166.candidate16683 14

certified_graph_case record001 31 29285906120704 GraphCoverageDescriptions.GraphCoverageBatch166.candidate16684 14

certified_graph_case record002 31 29292819939328 GraphCoverageDescriptions.GraphCoverageBatch166.candidate16685 14

certified_graph_case record003 31 29292956221440 GraphCoverageDescriptions.GraphCoverageBatch166.candidate16686 14

certified_graph_case record004 31 29293860126720 GraphCoverageDescriptions.GraphCoverageBatch166.candidate16687 14

theorem record005_parameters : Parameters record005 (rowOfCode 31) 29413079023744 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29413079023744 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch166.candidate16688 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 29413079023744
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch166.candidate16688_checked

theorem record005_result : Result (31, 29413079023744) :=
  of_direct_small 31 29413079023744 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00132.record005.direct_core, record005_parameters, record005_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00132

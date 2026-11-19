module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00154Checked
public import GraphInputsRow31Part00154Metadata
public import GraphInputsRow31Part00154Frames
public import GraphInputsRow31Part00154Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch167
public import GraphInputsRow31Part00154Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00154
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 31) 30875178246144 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 30875178246144 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16775 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 30875178246144
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch167.candidate16775_checked

theorem record000_result : Result (31, 30875178246144) :=
  of_direct_small 31 30875178246144 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00154.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 31 30880849469696 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16776 14

certified_graph_case record002 31 30900142407936 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16777 14

certified_graph_case record003 31 30900687601664 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16778 14

certified_graph_case record004 31 30900955906048 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16779 14

theorem record005_parameters : Parameters record005 (rowOfCode 31) 30907139391488 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 30907139391488 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16780 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 30907139391488
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch167.candidate16780_checked

theorem record005_result : Result (31, 30907139391488) :=
  of_direct_small 31 30907139391488 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00154.record005.direct_core, record005_parameters, record005_coverage⟩

certified_graph_case record006 31 30908732309760 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16781 14

theorem record007_parameters : Parameters record007 (rowOfCode 31) 30909537452544 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 30909537452544 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16782 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 30909537452544
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch167.candidate16782_checked

theorem record007_result : Result (31, 30909537452544) :=
  of_direct_small 31 30909537452544 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00154.record007.direct_core, record007_parameters, record007_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00154

module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00143Checked
public import GraphInputsRow29Part00143Metadata
public import GraphInputsRow29Part00143Frames
public import GraphInputsRow29Part00143Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch117
public import GraphCoverageBatch151
public import GraphInputsRow29Part00143Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00143
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 24276632633600 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15156 14

theorem record001_parameters : Parameters record001 (rowOfCode 29) 24276644143104 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24276644143104 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11739 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24276644143104
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch117.candidate11739_checked

theorem record001_result : Result (29, 24276644143104) :=
  of_direct_small 29 24276644143104 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00143.record001.direct_core, record001_parameters, record001_coverage⟩

theorem record002_parameters : Parameters record002 (rowOfCode 29) 24293610389760 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24293610389760 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11740 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24293610389760
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch117.candidate11740_checked

theorem record002_result : Result (29, 24293610389760) :=
  of_direct_small 29 24293610389760 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00143.record002.direct_core, record002_parameters, record002_coverage⟩

certified_graph_case record003 29 24299050172672 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15157 14

theorem record004_parameters : Parameters record004 (rowOfCode 29) 24299587043328 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24299587043328 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11741 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24299587043328
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch117.candidate11741_checked

theorem record004_result : Result (29, 24299587043328) :=
  of_direct_small 29 24299587043328 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00143.record004.direct_core, record004_parameters, record004_coverage⟩

certified_graph_case record005 29 24299595366400 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11742 14

certified_graph_case record006 29 24303747792896 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15158 14

certified_graph_case record007 29 24303756115968 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11743 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00143

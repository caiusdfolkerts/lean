module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00035Checked
public import GraphInputsRow31Part00035Metadata
public import GraphInputsRow31Part00035Frames
public import GraphInputsRow31Part00035Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch159
public import GraphInputsRow31Part00035Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00035
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 7373125058560 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15903 14

certified_graph_case record001 31 7432844148736 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15904 14

theorem record002_parameters : Parameters record002 (rowOfCode 31) 7478347563008 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 7478347563008 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15905 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 7478347563008
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch159.candidate15905_checked

theorem record002_result : Result (31, 7478347563008) :=
  of_direct_small 31 7478347563008 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00035.record002.direct_core, record002_parameters, record002_coverage⟩

theorem record003_parameters : Parameters record003 (rowOfCode 31) 7481971507200 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 7481971507200 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15906 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 7481971507200
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch159.candidate15906_checked

theorem record003_result : Result (31, 7481971507200) :=
  of_direct_small 31 7481971507200 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00035.record003.direct_core, record003_parameters, record003_coverage⟩

certified_graph_case record004 31 7516192932096 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15907 14

certified_graph_case record005 31 7516998074880 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15908 14

certified_graph_case record006 31 7533666238464 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15909 14

certified_graph_case record007 31 7550829330432 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15910 14

certified_graph_case record008 31 7551357812736 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15911 14

certified_graph_case record009 31 7560285421824 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15912 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00035

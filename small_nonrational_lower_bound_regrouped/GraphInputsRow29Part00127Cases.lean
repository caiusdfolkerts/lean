module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00127Checked
public import GraphInputsRow29Part00127Metadata
public import GraphInputsRow29Part00127Frames
public import GraphInputsRow29Part00127Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch116
public import GraphCoverageBatch149
public import GraphInputsRow29Part00127Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00127
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 21446517096704 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14992 14

certified_graph_case record001 29 21462623195264 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11653 14

certified_graph_case record002 29 21514045391104 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14993 14

certified_graph_case record003 29 21514053779456 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11654 14

certified_graph_case record004 29 21514837623040 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14994 14

certified_graph_case record005 29 21515110350848 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14995 14

theorem record006_parameters : Parameters record006 (rowOfCode 29) 21515374493696 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 21515374493696 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14996 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 21515374493696
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch149.candidate14996_checked

theorem record006_result : Result (29, 21515374493696) :=
  of_direct_small 29 21515374493696 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00127.record006.direct_core, record006_parameters, record006_coverage⟩
#print axioms record006_result

theorem record007_parameters : Parameters record007 (rowOfCode 29) 21515382816768 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 21515382816768 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11655 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 21515382816768
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch116.candidate11655_checked

theorem record007_result : Result (29, 21515382816768) :=
  of_direct_small 29 21515382816768 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00127.record007.direct_core, record007_parameters, record007_coverage⟩
#print axioms record007_result

certified_graph_case record008 29 21518998372608 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14997 14

certified_graph_case record009 29 21519271002112 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14998 14

certified_graph_case record010 29 21519535243264 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14999 14

certified_graph_case record011 29 21519543566336 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11656 14

certified_graph_case record012 29 21519667363840 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11657 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00127

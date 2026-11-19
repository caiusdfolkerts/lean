module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00152Checked
public import GraphInputsRow29Part00152Metadata
public import GraphInputsRow29Part00152Frames
public import GraphInputsRow29Part00152Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch117
public import GraphCoverageBatch151
public import GraphInputsRow29Part00152Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00152
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 24681635643392 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11766 14

certified_graph_case record001 29 24740171907328 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15191 14

certified_graph_case record002 29 24740171972608 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11767 14

certified_graph_case record003 29 24741314891776 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11768 14

theorem record004_parameters : Parameters record004 (rowOfCode 29) 24741322690576 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24741322690576 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11769 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24741322690576
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch117.candidate11769_checked

theorem record004_result : Result (29, 24741322690576) :=
  of_direct_small 29 24741322690576 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00152.record004.direct_core, record004_parameters, record004_coverage⟩
#print axioms record004_result

certified_graph_case record005 29 24741339465744 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11770 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00152

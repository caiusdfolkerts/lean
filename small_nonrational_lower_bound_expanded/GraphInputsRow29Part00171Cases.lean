module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00171Checked
public import GraphInputsRow29Part00171Metadata
public import GraphInputsRow29Part00171Frames
public import GraphInputsRow29Part00171Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch118
public import GraphCoverageBatch152
public import GraphInputsRow29Part00171Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00171
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 25735462928640 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15263 14

certified_graph_case record001 29 25739757944832 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11851 14

certified_graph_case record002 29 25739898388480 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11852 14

certified_graph_case record003 29 25740294750208 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11853 14

certified_graph_case record004 29 25740410355712 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11854 14

certified_graph_case record005 29 25752642797568 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15264 14

certified_graph_case record006 29 25756919021568 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15265 14

theorem record007_parameters : Parameters record007 (rowOfCode 29) 25769821618432 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25769821618432 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11855 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25769821618432
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch118.candidate11855_checked

theorem record007_result : Result (29, 25769821618432) :=
  of_direct_small 29 25769821618432 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00171.record007.direct_core, record007_parameters, record007_coverage⟩

theorem record008_parameters : Parameters record008 (rowOfCode 29) 25772110643200 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25772110643200 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11857 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25772110643200
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch118.candidate11857_checked

theorem record008_result : Result (29, 25772110643200) :=
  of_direct_small 29 25772110643200 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00171.record008.direct_core, record008_parameters, record008_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00171

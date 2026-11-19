module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00012Checked
public import GraphInputsRow29Part00012Metadata
public import GraphInputsRow29Part00012Frames
public import GraphInputsRow29Part00012Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch106
public import GraphCoverageBatch143
public import GraphInputsRow29Part00012Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00012
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 29) 3226195722240 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 3226195722240 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10673 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 3226195722240
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch106.candidate10673_checked

theorem record000_result : Result (29, 3226195722240) :=
  of_direct_small 29 3226195722240 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00012.record000.direct_core, record000_parameters, record000_coverage⟩

theorem record001_parameters : Parameters record001 (rowOfCode 29) 3232254459904 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 3232254459904 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10674 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 3232254459904
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch106.candidate10674_checked

theorem record001_result : Result (29, 3232254459904) :=
  of_direct_small 29 3232254459904 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00012.record001.direct_core, record001_parameters, record001_coverage⟩

certified_graph_case record002 29 3236530553088 GraphCoverageDescriptions.GraphCoverageBatch143.candidate14357 14

certified_graph_case record003 29 3237067423744 GraphCoverageDescriptions.GraphCoverageBatch143.candidate14358 14

certified_graph_case record004 29 3237075746816 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10675 14

theorem record005_parameters : Parameters record005 (rowOfCode 29) 3238693765120 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 3238693765120 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch143.candidate14359 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 3238693765120
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch143.candidate14359_checked

theorem record005_result : Result (29, 3238693765120) :=
  of_direct_small 29 3238693765120 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00012.record005.direct_core, record005_parameters, record005_coverage⟩

certified_graph_case record006 29 3240691302656 GraphCoverageDescriptions.GraphCoverageBatch143.candidate14360 14

theorem record007_parameters : Parameters record007 (rowOfCode 29) 3240955478784 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 3240955478784 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10676 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 3240955478784
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch106.candidate10676_checked

theorem record007_result : Result (29, 3240955478784) :=
  of_direct_small 29 3240955478784 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00012.record007.direct_core, record007_parameters, record007_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00012

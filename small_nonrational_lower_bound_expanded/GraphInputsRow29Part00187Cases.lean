module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00187Checked
public import GraphInputsRow29Part00187Metadata
public import GraphInputsRow29Part00187Frames
public import GraphInputsRow29Part00187Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch119
public import GraphCoverageBatch153
public import GraphInputsRow29Part00187Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00187
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 27222062665760 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15345 14

theorem record001_parameters : Parameters record001 (rowOfCode 29) 27224254726272 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 27224254726272 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11919 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 27224254726272
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch119.candidate11919_checked

theorem record001_result : Result (29, 27224254726272) :=
  of_direct_small 29 27224254726272 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00187.record001.direct_core, record001_parameters, record001_coverage⟩

certified_graph_case record002 29 27250632196352 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15346 14

theorem record003_parameters : Parameters record003 (rowOfCode 29) 27251301187584 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 27251301187584 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11920 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 27251301187584
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch119.candidate11920_checked

theorem record003_result : Result (29, 27251301187584) :=
  of_direct_small 29 27251301187584 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00187.record003.direct_core, record003_parameters, record003_coverage⟩

certified_graph_case record004 29 27257542311936 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11921 14

theorem record005_parameters : Parameters record005 (rowOfCode 29) 27258582499328 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 27258582499328 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11922 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 27258582499328
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch119.candidate11922_checked

theorem record005_result : Result (29, 27258582499328) :=
  of_direct_small 29 27258582499328 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00187.record005.direct_core, record005_parameters, record005_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00187

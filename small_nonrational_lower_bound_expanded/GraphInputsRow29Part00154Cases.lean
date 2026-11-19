module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00154Checked
public import GraphInputsRow29Part00154Metadata
public import GraphInputsRow29Part00154Frames
public import GraphInputsRow29Part00154Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch117
public import GraphCoverageBatch151
public import GraphCoverageBatch152
public import GraphInputsRow29Part00154Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00154
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 24779012768000 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15197 14

theorem record001_parameters : Parameters record001 (rowOfCode 29) 24779285495808 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24779285495808 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15198 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24779285495808
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch151.candidate15198_checked

theorem record001_result : Result (29, 24779285495808) :=
  of_direct_small 29 24779285495808 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00154.record001.direct_core, record001_parameters, record001_coverage⟩

certified_graph_case record002 29 24779549638656 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15199 14

certified_graph_case record003 29 24779557961728 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11775 14

certified_graph_case record004 29 24783173517568 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15200 14

certified_graph_case record005 29 24783446147072 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15201 14

certified_graph_case record006 29 24783710388224 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15202 14

theorem record007_parameters : Parameters record007 (rowOfCode 29) 24783718711296 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24783718711296 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11776 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24783718711296
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch117.candidate11776_checked

theorem record007_result : Result (29, 24783718711296) :=
  of_direct_small 29 24783718711296 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00154.record007.direct_core, record007_parameters, record007_coverage⟩

theorem record008_parameters : Parameters record008 (rowOfCode 29) 24783842508800 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24783842508800 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11777 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24783842508800
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch117.candidate11777_checked

theorem record008_result : Result (29, 24783842508800) :=
  of_direct_small 29 24783842508800 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00154.record008.direct_core, record008_parameters, record008_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00154

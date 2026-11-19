module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00177Checked
public import GraphInputsRow29Part00177Metadata
public import GraphInputsRow29Part00177Frames
public import GraphInputsRow29Part00177Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch118
public import GraphCoverageBatch152
public import GraphInputsRow29Part00177Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00177
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 25916906602752 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15278 14

certified_graph_case record001 29 25924439933184 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15279 14

certified_graph_case record002 29 25924980965376 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11874 14

theorem record003_parameters : Parameters record003 (rowOfCode 29) 25925228171264 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25925228171264 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11875 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25925228171264
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch118.candidate11875_checked

theorem record003_result : Result (29, 25925228171264) :=
  of_direct_small 29 25925228171264 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00177.record003.direct_core, record003_parameters, record003_coverage⟩

certified_graph_case record004 29 25925496504576 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15280 14

theorem record005_parameters : Parameters record005 (rowOfCode 29) 25926301647360 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25926301647360 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11876 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25926301647360
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch118.candidate11876_checked

theorem record005_result : Result (29, 25926301647360) :=
  of_direct_small 29 25926301647360 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00177.record005.direct_core, record005_parameters, record005_coverage⟩

certified_graph_case record006 29 25928755380224 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15281 14

certified_graph_case record007 29 25933012668672 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11877 14

certified_graph_case record008 29 25963354128384 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11878 14

theorem record009_parameters : Parameters record009 (rowOfCode 29) 25980811411456 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25980811411456 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11879 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25980811411456
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.small_allowed record009 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch118.candidate11879_checked

theorem record009_result : Result (29, 25980811411456) :=
  of_direct_small 29 25980811411456 (by decide) ⟨record009, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00177.record009.direct_core, record009_parameters, record009_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00177

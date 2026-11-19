module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00037Checked
public import GraphInputsRow29Part00037Metadata
public import GraphInputsRow29Part00037Frames
public import GraphInputsRow29Part00037Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch109
public import GraphCoverageBatch144
public import GraphInputsRow29Part00037Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00037
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 7435204956160 GraphCoverageDescriptions.GraphCoverageBatch144.candidate14448 14

certified_graph_case record001 29 7478343369344 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10917 14

certified_graph_case record002 29 7518138925056 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10918 14

certified_graph_case record003 29 7525072437248 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10919 14

certified_graph_case record004 29 7533641206016 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10920 14

theorem record005_parameters : Parameters record005 (rowOfCode 29) 7533657850624 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 7533657850624 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10921 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 7533657850624
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch109.candidate10921_checked

theorem record005_result : Result (29, 7533657850624) :=
  of_direct_small 29 7533657850624 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00037.record005.direct_core, record005_parameters, record005_coverage⟩

theorem record006_parameters : Parameters record006 (rowOfCode 29) 7533938868224 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 7533938868224 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10922 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 7533938868224
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch109.candidate10922_checked

theorem record006_result : Result (29, 7533938868224) :=
  of_direct_small 29 7533938868224 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00037.record006.direct_core, record006_parameters, record006_coverage⟩

certified_graph_case record007 29 7534178271232 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10923 14

theorem record008_parameters : Parameters record008 (rowOfCode 29) 7542768173056 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 7542768173056 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10924 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 7542768173056
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch109.candidate10924_checked

theorem record008_result : Result (29, 7542768173056) :=
  of_direct_small 29 7542768173056 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00037.record008.direct_core, record008_parameters, record008_coverage⟩

certified_graph_case record009 29 7550552670464 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10925 14

certified_graph_case record010 29 7551357813248 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10926 14

certified_graph_case record011 29 7551374589952 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10927 14

theorem record012_parameters : Parameters record012 (rowOfCode 29) 7560302199040 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record012_coverage : Coverage record012 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 7560302199040 :=
  GraphCoverageDescriptions.coverage_of_checked record012 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10928 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 7560302199040
    (by rfl) record012_cells_exact
    (GraphCoverageDescriptions.small_allowed record012 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch109.candidate10928_checked

theorem record012_result : Result (29, 7560302199040) :=
  of_direct_small 29 7560302199040 (by decide) ⟨record012, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00037.record012.direct_core, record012_parameters, record012_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00037

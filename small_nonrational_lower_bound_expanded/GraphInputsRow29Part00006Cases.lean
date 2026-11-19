module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00006Checked
public import GraphInputsRow29Part00006Metadata
public import GraphInputsRow29Part00006Frames
public import GraphInputsRow29Part00006Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch105
public import GraphCoverageBatch106
public import GraphCoverageBatch143
public import GraphInputsRow29Part00006Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00006
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 2004013875200 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10596 14

certified_graph_case record001 29 2004174799104 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10597 14

certified_graph_case record002 29 2015157551105 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10598 14

certified_graph_case record003 29 2019442065664 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10599 14

certified_graph_case record004 29 2019452518401 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10600 14

certified_graph_case record005 29 2019452534784 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10601 14

theorem record006_parameters : Parameters record006 (rowOfCode 29) 2019777609984 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 2019777609984 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10602 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 2019777609984
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch106.candidate10602_checked

theorem record006_result : Result (29, 2019777609984) :=
  of_direct_small 29 2019777609984 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00006.record006.direct_core, record006_parameters, record006_coverage⟩

theorem record007_parameters : Parameters record007 (rowOfCode 29) 2019913957376 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 2019913957376 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10603 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 2019913957376
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch106.candidate10603_checked

theorem record007_result : Result (29, 2019913957376) :=
  of_direct_small 29 2019913957376 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00006.record007.direct_core, record007_parameters, record007_coverage⟩

theorem record008_parameters : Parameters record008 (rowOfCode 29) 2019922280448 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 2019922280448 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10604 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 2019922280448
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch106.candidate10604_checked

theorem record008_result : Result (29, 2019922280448) :=
  of_direct_small 29 2019922280448 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00006.record008.direct_core, record008_parameters, record008_coverage⟩

certified_graph_case record009 29 2020318642176 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10605 14

certified_graph_case record010 29 2031809003776 GraphCoverageDescriptions.GraphCoverageBatch143.candidate14330 14

theorem record011_parameters : Parameters record011 (rowOfCode 29) 2031817392128 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record011_coverage : Coverage record011 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 2031817392128 :=
  GraphCoverageDescriptions.coverage_of_checked record011 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10606 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 2031817392128
    (by rfl) record011_cells_exact
    (GraphCoverageDescriptions.small_allowed record011 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch106.candidate10606_checked

theorem record011_result : Result (29, 2031817392128) :=
  of_direct_small 29 2031817392128 (by decide) ⟨record011, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00006.record011.direct_core, record011_parameters, record011_coverage⟩

certified_graph_case record012 29 2032325132544 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10607 14

certified_graph_case record013 29 2032337422336 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10608 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00006

module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00011Checked
public import GraphInputsRow29Part00011Metadata
public import GraphInputsRow29Part00011Frames
public import GraphInputsRow29Part00011Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch106
public import GraphInputsRow29Part00011Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00011
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 3208479047936 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10665 14

certified_graph_case record001 29 3208743224064 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10666 14

certified_graph_case record002 29 3209015918592 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10667 14

theorem record003_parameters : Parameters record003 (rowOfCode 29) 3209024241664 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 3209024241664 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10668 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 3209024241664
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch106.candidate10668_checked

theorem record003_result : Result (29, 3209024241664) :=
  of_direct_small 29 3209024241664 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00011.record003.direct_core, record003_parameters, record003_coverage⟩

certified_graph_case record004 29 3217068949760 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10669 14

certified_graph_case record005 29 3217737940992 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10670 14

theorem record006_parameters : Parameters record006 (rowOfCode 29) 3225658916864 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 3225658916864 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10671 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 3225658916864
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch106.candidate10671_checked

theorem record006_result : Result (29, 3225658916864) :=
  of_direct_small 29 3225658916864 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00011.record006.direct_core, record006_parameters, record006_coverage⟩

certified_graph_case record007 29 3225931481088 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10672 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00011

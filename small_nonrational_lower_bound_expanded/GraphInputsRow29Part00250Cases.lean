module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00250Checked
public import GraphInputsRow29Part00250Metadata
public import GraphInputsRow29Part00250Frames
public import GraphInputsRow29Part00250Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch121
public import GraphCoverageBatch122
public import GraphInputsRow29Part00250Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00250
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 32198434553856 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12197 14

certified_graph_case record001 29 32199103479808 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12198 14

certified_graph_case record002 29 32205344604160 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12199 14

theorem record003_parameters : Parameters record003 (rowOfCode 29) 32270513602560 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32270513602560 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch122.candidate12200 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 32270513602560
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch122.candidate12200_checked

theorem record003_result : Result (29, 32270513602560) :=
  of_direct_small 29 32270513602560 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00250.record003.direct_core, record003_parameters, record003_coverage⟩

theorem record004_parameters : Parameters record004 (rowOfCode 29) 32271042084864 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32271042084864 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch122.candidate12201 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 32271042084864
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch122.candidate12201_checked

theorem record004_result : Result (29, 32271042084864) :=
  of_direct_small 29 32271042084864 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00250.record004.direct_core, record004_parameters, record004_coverage⟩

theorem record005_parameters : Parameters record005 (rowOfCode 29) 32301981368320 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32301981368320 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch122.candidate12202 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 32301981368320
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch122.candidate12202_checked

theorem record005_result : Result (29, 32301981368320) :=
  of_direct_small 29 32301981368320 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00250.record005.direct_core, record005_parameters, record005_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00250

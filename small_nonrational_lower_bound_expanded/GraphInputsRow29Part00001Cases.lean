module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00001Checked
public import GraphInputsRow29Part00001Metadata
public import GraphInputsRow29Part00001Frames
public import GraphInputsRow29Part00001Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch105
public import GraphCoverageBatch143
public import GraphInputsRow29Part00001Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 819139182592 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10521 14

certified_graph_case record001 29 872562065664 GraphCoverageDescriptions.GraphCoverageBatch143.candidate14312 14

certified_graph_case record002 29 872562130944 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10522 14

certified_graph_case record003 29 881286201472 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10523 14

certified_graph_case record004 29 915645931648 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10524 14

certified_graph_case record005 29 938857267456 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10525 14

certified_graph_case record006 29 938865655808 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10526 14

theorem record007_parameters : Parameters record007 (rowOfCode 29) 1003281776896 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 1003281776896 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10527 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 1003281776896
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch105.candidate10527_checked

theorem record007_result : Result (29, 1003281776896) :=
  of_direct_small 29 1003281776896 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00001.record007.direct_core, record007_parameters, record007_coverage⟩

certified_graph_case record008 29 1003290165248 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10528 14

theorem record009_parameters : Parameters record009 (rowOfCode 29) 1003682300160 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 1003682300160 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10529 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 1003682300160
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.small_allowed record009 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch105.candidate10529_checked

theorem record009_result : Result (29, 1003682300160) :=
  of_direct_small 29 1003682300160 (by decide) ⟨record009, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00001.record009.direct_core, record009_parameters, record009_coverage⟩

theorem record010_parameters : Parameters record010 (rowOfCode 29) 1007583035392 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record010_coverage : Coverage record010 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 1007583035392 :=
  GraphCoverageDescriptions.coverage_of_checked record010 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10530 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 1007583035392
    (by rfl) record010_cells_exact
    (GraphCoverageDescriptions.small_allowed record010 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch105.candidate10530_checked

theorem record010_result : Result (29, 1007583035392) :=
  of_direct_small 29 1007583035392 (by decide) ⟨record010, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00001.record010.direct_core, record010_parameters, record010_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001

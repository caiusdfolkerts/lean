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
#print axioms record007_result

certified_graph_case record008 29 1003290165248 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10528 14

certified_graph_case record009 29 1003682300160 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10529 14

certified_graph_case record010 29 1007583035392 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10530 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00001

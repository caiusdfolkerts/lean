module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00015Checked
public import GraphInputsRow29Part00015Metadata
public import GraphInputsRow29Part00015Frames
public import GraphInputsRow29Part00015Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch106
public import GraphCoverageBatch107
public import GraphInputsRow29Part00015Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 3853839794432 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10694 14

theorem record001_parameters : Parameters record001 (rowOfCode 29) 3853967753472 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 3853967753472 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10695 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 3853967753472
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch106.candidate10695_checked

theorem record001_result : Result (29, 3853967753472) :=
  of_direct_small 29 3853967753472 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00015.record001.direct_core, record001_parameters, record001_coverage⟩
#print axioms record001_result

theorem record002_parameters : Parameters record002 (rowOfCode 29) 3853971915008 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 3853971915008 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10696 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 3853971915008
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch106.candidate10696_checked

theorem record002_result : Result (29, 3853971915008) :=
  of_direct_small 29 3853971915008 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00015.record002.direct_core, record002_parameters, record002_coverage⟩
#print axioms record002_result

certified_graph_case record003 29 3853971980288 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10697 14

certified_graph_case record004 29 3854074646784 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10698 14

certified_graph_case record005 29 3861859274768 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10699 14

certified_graph_case record006 29 3866953257216 GraphCoverageDescriptions.GraphCoverageBatch107.candidate10700 14

certified_graph_case record007 29 3921595138304 GraphCoverageDescriptions.GraphCoverageBatch107.candidate10701 14

theorem record008_parameters : Parameters record008 (rowOfCode 29) 3921599299840 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 3921599299840 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch107.candidate10702 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 3921599299840
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch107.candidate10702_checked

theorem record008_result : Result (29, 3921599299840) :=
  of_direct_small 29 3921599299840 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00015.record008.direct_core, record008_parameters, record008_coverage⟩
#print axioms record008_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015

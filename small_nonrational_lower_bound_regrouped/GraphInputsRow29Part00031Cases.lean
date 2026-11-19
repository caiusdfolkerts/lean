module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00031Checked
public import GraphInputsRow29Part00031Metadata
public import GraphInputsRow29Part00031Frames
public import GraphInputsRow29Part00031Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch108
public import GraphCoverageBatch144
public import GraphInputsRow29Part00031Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00031
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 6995161677824 GraphCoverageDescriptions.GraphCoverageBatch144.candidate14424 14

certified_graph_case record001 29 6999458709504 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10865 14

certified_graph_case record002 29 7003082653696 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10866 14

certified_graph_case record003 29 7003355217920 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10867 14

theorem record004_parameters : Parameters record004 (rowOfCode 29) 7003619459072 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 7003619459072 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10868 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 7003619459072
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch108.candidate10868_checked

theorem record004_result : Result (29, 7003619459072) :=
  of_direct_small 29 7003619459072 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00031.record004.direct_core, record004_parameters, record004_coverage⟩
#print axioms record004_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00031

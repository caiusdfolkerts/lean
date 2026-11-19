module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00027Checked
public import GraphInputsRow29Part00027Metadata
public import GraphInputsRow29Part00027Frames
public import GraphInputsRow29Part00027Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch108
public import GraphCoverageBatch144
public import GraphInputsRow29Part00027Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00027
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 6711570137088 GraphCoverageDescriptions.GraphCoverageBatch144.candidate14415 14

certified_graph_case record001 29 6720160038912 GraphCoverageDescriptions.GraphCoverageBatch144.candidate14416 14

certified_graph_case record002 29 6727198113792 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10840 14

theorem record003_parameters : Parameters record003 (rowOfCode 29) 6727206436864 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 6727206436864 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10841 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 6727206436864
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch108.candidate10841_checked

theorem record003_result : Result (29, 6727206436864) :=
  of_direct_small 29 6727206436864 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00027.record003.direct_core, record003_parameters, record003_coverage⟩
#print axioms record003_result

certified_graph_case record004 29 6738963693600 GraphCoverageDescriptions.GraphCoverageBatch144.candidate14417 14

certified_graph_case record005 29 6752966836480 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10842 14

certified_graph_case record006 29 6791622623232 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10843 14

certified_graph_case record007 29 6791630946304 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10844 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00027

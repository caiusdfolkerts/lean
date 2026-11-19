module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00216Checked
public import GraphInputsRow29Part00216Metadata
public import GraphInputsRow29Part00216Frames
public import GraphInputsRow29Part00216Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch120
public import GraphInputsRow29Part00216Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00216
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 29584137652224 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12020 14

certified_graph_case record001 29 29588029835392 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12021 14

certified_graph_case record002 29 29588298270720 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12022 14

theorem record003_parameters : Parameters record003 (rowOfCode 29) 29588314915328 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29588314915328 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12023 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 29588314915328
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch120.candidate12023_checked

theorem record003_result : Result (29, 29588314915328) :=
  of_direct_small 29 29588314915328 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00216.record003.direct_core, record003_parameters, record003_coverage⟩
#print axioms record003_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00216

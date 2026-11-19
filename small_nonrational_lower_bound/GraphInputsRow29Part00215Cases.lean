module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00215Checked
public import GraphInputsRow29Part00215Metadata
public import GraphInputsRow29Part00215Frames
public import GraphInputsRow29Part00215Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch120
public import GraphInputsRow29Part00215Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00215
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 29) 29552998875648 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29552998875648 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12016 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 29552998875648
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch120.candidate12016_checked

theorem record000_result : Result (29, 29552998875648) :=
  of_direct_small 29 29552998875648 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00215.record000.direct_core, record000_parameters, record000_coverage⟩
#print axioms record000_result

certified_graph_case record001 29 29583751790720 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12017 14

certified_graph_case record002 29 29583886024704 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12018 14

certified_graph_case record003 29 29583890186240 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12019 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00215

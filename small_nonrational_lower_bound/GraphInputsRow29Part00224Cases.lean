module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00224Checked
public import GraphInputsRow29Part00224Metadata
public import GraphInputsRow29Part00224Frames
public import GraphInputsRow29Part00224Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch120
public import GraphCoverageBatch154
public import GraphInputsRow29Part00224Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00224
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 30314164977664 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15453 14

certified_graph_case record001 29 30314416179216 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12059 14

certified_graph_case record002 29 30314432823824 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12060 14

certified_graph_case record003 29 30315363958784 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12061 14

theorem record004_parameters : Parameters record004 (rowOfCode 29) 30378589487104 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 30378589487104 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12062 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 30378589487104
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch120.candidate12062_checked

theorem record004_result : Result (29, 30378589487104) :=
  of_direct_small 29 30378589487104 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00224.record004.direct_core, record004_parameters, record004_coverage⟩
#print axioms record004_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00224

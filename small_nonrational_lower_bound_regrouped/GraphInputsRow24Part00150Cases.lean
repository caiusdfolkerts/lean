module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00150Checked
public import GraphInputsRow24Part00150Metadata
public import GraphInputsRow24Part00150Frames
public import GraphInputsRow24Part00150Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch102
public import GraphInputsRow24Part00150Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00150
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 32513456611584 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10245 14

certified_graph_case record001 24 32513464999936 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10246 14

theorem record002_parameters : Parameters record002 (rowOfCode 24) 32513465520128 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32513465520128 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10247 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 32513465520128
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch102.candidate10247_checked

theorem record002_result : Result (24, 32513465520128) :=
  of_direct_small 24 32513465520128 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00150.record002.direct_core, record002_parameters, record002_coverage⟩
#print axioms record002_result

certified_graph_case record003 24 32513506676992 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10248 14

certified_graph_case record004 24 32514521571328 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10249 14

certified_graph_case record005 24 32514547712000 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10250 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00150

module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00212Checked
public import GraphInputsRow29Part00212Metadata
public import GraphInputsRow29Part00212Frames
public import GraphInputsRow29Part00212Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch120
public import GraphCoverageBatch154
public import GraphInputsRow29Part00212Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00212
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 29285637750784 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15429 14

certified_graph_case record001 29 29285905596944 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15430 14

theorem record002_parameters : Parameters record002 (rowOfCode 29) 29291878551680 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29291878551680 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 29291878551680
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch120.candidate12005_checked

theorem record002_result : Result (29, 29291878551680) :=
  of_direct_small 29 29291878551680 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00212.record002.direct_core, record002_parameters, record002_coverage⟩
#print axioms record002_result

certified_graph_case record003 29 29292952027776 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15431 14

certified_graph_case record004 29 29414235078784 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15432 14

certified_graph_case record005 29 29414375034880 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12007 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00212

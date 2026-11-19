module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00207Checked
public import GraphInputsRow29Part00207Metadata
public import GraphInputsRow29Part00207Frames
public import GraphInputsRow29Part00207Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch119
public import GraphCoverageBatch154
public import GraphInputsRow29Part00207Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00207
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 29147295416320 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11991 14

certified_graph_case record001 29 29147326333056 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15407 14

certified_graph_case record002 29 29148198736128 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15408 14

certified_graph_case record003 29 29148467171456 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15409 14

theorem record004_parameters : Parameters record004 (rowOfCode 29) 29155513630848 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29155513630848 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15410 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 29155513630848
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch154.candidate15410_checked

theorem record004_result : Result (29, 29155513630848) :=
  of_direct_small 29 29155513630848 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00207.record004.direct_core, record004_parameters, record004_coverage⟩
#print axioms record004_result

certified_graph_case record005 29 29155647832192 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15411 14

certified_graph_case record006 29 29155653586944 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15412 14

certified_graph_case record007 29 29175998611712 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15413 14

certified_graph_case record008 29 29176002838528 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11992 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00207

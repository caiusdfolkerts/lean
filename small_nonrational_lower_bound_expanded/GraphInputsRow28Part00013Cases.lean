module
prelude
public meta import GraphCases
public import GraphInputsRow28Part00013Checked
public import GraphInputsRow28Part00013Metadata
public import GraphInputsRow28Part00013Frames
public import GraphInputsRow28Part00013Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch142
public import GraphCoverageBatch143
public import GraphInputsRow28Part00013Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00013
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 28 34746822295552 GraphCoverageDescriptions.GraphCoverageBatch142.candidate14298 6

certified_graph_case record001 28 34763465293824 GraphCoverageDescriptions.GraphCoverageBatch142.candidate14299 6

certified_graph_case record002 28 34772072595456 GraphCoverageDescriptions.GraphCoverageBatch143.candidate14300 6

certified_graph_case record003 28 34789252399104 GraphCoverageDescriptions.GraphCoverageBatch143.candidate14301 6

certified_graph_case record004 28 34790308970496 GraphCoverageDescriptions.GraphCoverageBatch143.candidate14302 6

certified_graph_case record005 28 34840799870976 GraphCoverageDescriptions.GraphCoverageBatch143.candidate14303 6

certified_graph_case record006 28 34892314312704 GraphCoverageDescriptions.GraphCoverageBatch143.candidate14304 6

certified_graph_case record007 28 35046933268480 GraphCoverageDescriptions.GraphCoverageBatch143.candidate14305 6

theorem record008_parameters : Parameters record008 (rowOfCode 28) 35115669389312 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 35115669389312 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch143.candidate14306 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 35115669389312
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch143.candidate14306_checked

theorem record008_result : Result (28, 35115669389312) :=
  of_direct_small 28 35115669389312 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow28Part00013.record008.direct_core, record008_parameters, record008_coverage⟩

certified_graph_case record009 28 35150012350464 GraphCoverageDescriptions.GraphCoverageBatch143.candidate14307 6
end Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00013

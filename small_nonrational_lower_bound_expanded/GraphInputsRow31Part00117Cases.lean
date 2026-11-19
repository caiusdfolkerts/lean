module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00117Checked
public import GraphInputsRow31Part00117Metadata
public import GraphInputsRow31Part00117Frames
public import GraphInputsRow31Part00117Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch165
public import GraphInputsRow31Part00117Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00117
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 26467065929984 GraphCoverageDescriptions.GraphCoverageBatch165.candidate16588 14

certified_graph_case record001 31 26468139147520 GraphCoverageDescriptions.GraphCoverageBatch165.candidate16589 14

theorem record002_parameters : Parameters record002 (rowOfCode 31) 26498610298880 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 26498610298880 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch165.candidate16590 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 26498610298880
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch165.candidate16590_checked

theorem record002_result : Result (31, 26498610298880) :=
  of_direct_small 31 26498610298880 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00117.record002.direct_core, record002_parameters, record002_coverage⟩

certified_graph_case record003 31 26498618621952 GraphCoverageDescriptions.GraphCoverageBatch165.candidate16591 14

certified_graph_case record004 31 26502498353920 GraphCoverageDescriptions.GraphCoverageBatch165.candidate16592 14

certified_graph_case record005 31 26502779371520 GraphCoverageDescriptions.GraphCoverageBatch165.candidate16593 14

certified_graph_case record006 31 26511100870656 GraphCoverageDescriptions.GraphCoverageBatch165.candidate16594 14

certified_graph_case record007 31 26511493070848 GraphCoverageDescriptions.GraphCoverageBatch165.candidate16595 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00117

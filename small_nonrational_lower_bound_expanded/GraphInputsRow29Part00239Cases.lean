module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00239Checked
public import GraphInputsRow29Part00239Metadata
public import GraphInputsRow29Part00239Frames
public import GraphInputsRow29Part00239Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch121
public import GraphCoverageBatch155
public import GraphInputsRow29Part00239Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00239
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 31544458674432 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15508 14

certified_graph_case record001 29 31568009765120 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15509 14

theorem record002_parameters : Parameters record002 (rowOfCode 29) 31568077848576 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31568077848576 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12159 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 31568077848576
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch121.candidate12159_checked

theorem record002_result : Result (29, 31568077848576) :=
  of_direct_small 29 31568077848576 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00239.record002.direct_core, record002_parameters, record002_coverage⟩

certified_graph_case record003 29 31579023933440 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15510 14

certified_graph_case record004 29 31587882237952 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12160 14

certified_graph_case record005 29 31596203737088 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12161 14

certified_graph_case record006 29 31596732219392 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12162 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00239

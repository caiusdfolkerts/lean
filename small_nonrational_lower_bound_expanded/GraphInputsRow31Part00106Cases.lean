module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00106Checked
public import GraphInputsRow31Part00106Metadata
public import GraphInputsRow31Part00106Frames
public import GraphInputsRow31Part00106Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch165
public import GraphInputsRow31Part00106Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00106
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 24417695432704 GraphCoverageDescriptions.GraphCoverageBatch165.candidate16511 14

certified_graph_case record001 31 24421253316608 GraphCoverageDescriptions.GraphCoverageBatch165.candidate16512 14

certified_graph_case record002 31 24473277833280 GraphCoverageDescriptions.GraphCoverageBatch165.candidate16513 14

theorem record003_parameters : Parameters record003 (rowOfCode 31) 24512185761792 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24512185761792 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch165.candidate16514 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24512185761792
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch165.candidate16514_checked

theorem record003_result : Result (31, 24512185761792) :=
  of_direct_small 31 24512185761792 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00106.record003.direct_core, record003_parameters, record003_coverage⟩

certified_graph_case record004 31 24573932208128 GraphCoverageDescriptions.GraphCoverageBatch165.candidate16515 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00106

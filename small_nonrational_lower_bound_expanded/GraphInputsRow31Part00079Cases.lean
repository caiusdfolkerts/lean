module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00079Checked
public import GraphInputsRow31Part00079Metadata
public import GraphInputsRow31Part00079Frames
public import GraphInputsRow31Part00079Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch162
public import GraphInputsRow31Part00079Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00079
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 15540936507936 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16230 14

certified_graph_case record001 31 15548924592384 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16231 14

certified_graph_case record002 31 15549259120640 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16232 14

certified_graph_case record003 31 15549527523328 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16233 14

theorem record004_parameters : Parameters record004 (rowOfCode 31) 15584427311104 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 15584427311104 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16234 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 15584427311104
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch162.candidate16234_checked

theorem record004_result : Result (31, 15584427311104) :=
  of_direct_small 31 15584427311104 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00079.record004.direct_core, record004_parameters, record004_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00079

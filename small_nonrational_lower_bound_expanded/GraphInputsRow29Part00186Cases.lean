module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00186Checked
public import GraphInputsRow29Part00186Metadata
public import GraphInputsRow29Part00186Frames
public import GraphInputsRow29Part00186Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch119
public import GraphInputsRow29Part00186Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00186
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 27128693293056 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11914 14

certified_graph_case record001 29 27130373144576 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11915 14

certified_graph_case record002 29 27130645708800 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11916 14

certified_graph_case record003 29 27130909949952 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11917 14

theorem record004_parameters : Parameters record004 (rowOfCode 29) 27217505554464 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 27217505554464 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11918 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 27217505554464
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch119.candidate11918_checked

theorem record004_result : Result (29, 27217505554464) :=
  of_direct_small 29 27217505554464 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00186.record004.direct_core, record004_parameters, record004_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00186

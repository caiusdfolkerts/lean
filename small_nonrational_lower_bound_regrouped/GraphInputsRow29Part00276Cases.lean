module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00276Checked
public import GraphInputsRow29Part00276Metadata
public import GraphInputsRow29Part00276Frames
public import GraphInputsRow29Part00276Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch122
public import GraphInputsRow29Part00276Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00276
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 29) 34125394215424 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34125394215424 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch122.candidate12294 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 34125394215424
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch122.candidate12294_checked

theorem record000_result : Result (29, 34125394215424) :=
  of_direct_small 29 34125394215424 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00276.record000.direct_core, record000_parameters, record000_coverage⟩
#print axioms record000_result

certified_graph_case record001 29 34127827452160 GraphCoverageDescriptions.GraphCoverageBatch122.candidate12295 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00276

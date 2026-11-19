module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00158Checked
public import GraphInputsRow29Part00158Metadata
public import GraphInputsRow29Part00158Frames
public import GraphInputsRow29Part00158Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch117
public import GraphInputsRow29Part00158Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00158
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 29) 25155357114368 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25155357114368 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11789 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25155357114368
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch117.candidate11789_checked

theorem record000_result : Result (29, 25155357114368) :=
  of_direct_small 29 25155357114368 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00158.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 29 25158081314816 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11790 14

certified_graph_case record002 29 25161061433344 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11791 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00158

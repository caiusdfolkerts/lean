module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00190Checked
public import GraphInputsRow29Part00190Metadata
public import GraphInputsRow29Part00190Frames
public import GraphInputsRow29Part00190Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch119
public import GraphCoverageBatch153
public import GraphInputsRow29Part00190Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00190
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 29) 27671000055808 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 27671000055808 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15357 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 27671000055808
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch153.candidate15357_checked

theorem record000_result : Result (29, 27671000055808) :=
  of_direct_small 29 27671000055808 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00190.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 29 27673145377536 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15358 14

certified_graph_case record002 29 27685428412672 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15359 14

certified_graph_case record003 29 27747774693376 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15360 14

certified_graph_case record004 29 27748443619328 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11928 14

theorem record005_parameters : Parameters record005 (rowOfCode 29) 27756368756736 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 27756368756736 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11929 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 27756368756736
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch119.candidate11929_checked

theorem record005_result : Result (29, 27756368756736) :=
  of_direct_small 29 27756368756736 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00190.record005.direct_core, record005_parameters, record005_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00190

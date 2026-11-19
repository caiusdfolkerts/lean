module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00042Checked
public import GraphInputsRow31Part00042Metadata
public import GraphInputsRow31Part00042Frames
public import GraphInputsRow31Part00042Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch159
public import GraphInputsRow31Part00042Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00042
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 31) 8267846156544 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8267846156544 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15947 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8267846156544
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch159.candidate15947_checked

theorem record000_result : Result (31, 8267846156544) :=
  of_direct_small 31 8267846156544 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00042.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 31 8268617879552 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15948 14

certified_graph_case record002 31 8323663986944 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15949 14

certified_graph_case record003 31 8324200857600 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15950 14

certified_graph_case record004 31 8324209180672 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15951 14

certified_graph_case record005 31 8324720558336 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15952 14

certified_graph_case record006 31 8325265752064 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15953 14

certified_graph_case record007 31 8332253888768 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15954 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00042

module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00193Checked
public import GraphInputsRow29Part00193Metadata
public import GraphInputsRow29Part00193Frames
public import GraphInputsRow29Part00193Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch119
public import GraphCoverageBatch153
public import GraphInputsRow29Part00193Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00193
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 29) 28072061702400 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 28072061702400 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11933 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 28072061702400
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch119.candidate11933_checked

theorem record000_result : Result (29, 28072061702400) :=
  of_direct_small 29 28072061702400 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00193.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 29 28076495339521 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11934 14

certified_graph_case record002 29 28082245271552 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15364 14

certified_graph_case record003 29 28082253594624 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11935 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00193

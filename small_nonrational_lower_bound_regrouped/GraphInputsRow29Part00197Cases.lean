module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00197Checked
public import GraphInputsRow29Part00197Metadata
public import GraphInputsRow29Part00197Frames
public import GraphInputsRow29Part00197Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch119
public import GraphCoverageBatch153
public import GraphInputsRow29Part00197Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00197
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 28627837141120 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11945 14

certified_graph_case record001 29 28628519751680 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15382 14

certified_graph_case record002 29 28628776157312 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15383 14

certified_graph_case record003 29 28628910358656 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15384 14

certified_graph_case record004 29 28631537582080 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11946 14

theorem record005_parameters : Parameters record005 (rowOfCode 29) 28640119128192 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 28640119128192 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11947 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 28640119128192
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch119.candidate11947_checked

theorem record005_result : Result (29, 28640119128192) :=
  of_direct_small 29 28640119128192 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00197.record005.direct_core, record005_parameters, record005_coverage⟩
#print axioms record005_result

certified_graph_case record006 29 28640123322368 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11948 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00197

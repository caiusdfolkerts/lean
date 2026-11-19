module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00291Checked
public import GraphInputsRow29Part00291Metadata
public import GraphInputsRow29Part00291Frames
public import GraphInputsRow29Part00291Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch123
public import GraphInputsRow29Part00291Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00291
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 34737716527104 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12353 14

certified_graph_case record001 29 34739046055936 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12354 14

certified_graph_case record002 29 34747896037376 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12355 14

theorem record003_parameters : Parameters record003 (rowOfCode 29) 34763465424896 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34763465424896 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12356 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 34763465424896
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch123.candidate12356_checked

theorem record003_result : Result (29, 34763465424896) :=
  of_direct_small 29 34763465424896 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00291.record003.direct_core, record003_parameters, record003_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00291

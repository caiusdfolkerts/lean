module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00285Checked
public import GraphInputsRow29Part00285Metadata
public import GraphInputsRow29Part00285Frames
public import GraphInputsRow29Part00285Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch123
public import GraphCoverageBatch155
public import GraphInputsRow29Part00285Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00285
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 34636227020816 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15535 14

certified_graph_case record001 29 34636243665424 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12332 14

certified_graph_case record002 29 34636495589376 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12333 14

theorem record003_parameters : Parameters record003 (rowOfCode 29) 34640022798336 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34640022798336 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12334 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 34640022798336
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch123.candidate12334_checked

theorem record003_result : Result (29, 34640022798336) :=
  of_direct_small 29 34640022798336 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00285.record003.direct_core, record003_parameters, record003_coverage⟩

theorem record004_parameters : Parameters record004 (rowOfCode 29) 34640295362560 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34640295362560 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12335 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 34640295362560
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch123.candidate12335_checked

theorem record004_result : Result (29, 34640295362560) :=
  of_direct_small 29 34640295362560 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00285.record004.direct_core, record004_parameters, record004_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00285

module
prelude
public meta import GraphCases
public import GraphInputsRow26Part00085Checked
public import GraphInputsRow26Part00085Metadata
public import GraphInputsRow26Part00085Frames
public import GraphInputsRow26Part00085Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch104
public import GraphInputsRow26Part00085Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 26 34681861050624 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10453 14

certified_graph_case record001 26 34681895059456 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10454 14

certified_graph_case record002 26 34682976600064 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10455 14

certified_graph_case record003 26 34699074863104 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10457 14

certified_graph_case record004 26 34703629619200 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10458 14

certified_graph_case record005 26 34712462690320 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10459 14

certified_graph_case record006 26 34712479334928 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10460 14

certified_graph_case record007 26 34737712824576 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10461 14

certified_graph_case record008 26 34738790268928 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10462 14

certified_graph_case record009 26 34739062833152 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10463 14

theorem record010_parameters : Parameters record010 (rowOfCode 26) 34739574800384 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record010_coverage : Coverage record010 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34739574800384 :=
  GraphCoverageDescriptions.coverage_of_checked record010 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10464 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 34739574800384
    (by rfl) record010_cells_exact
    (GraphCoverageDescriptions.small_allowed record010 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch104.candidate10464_checked

theorem record010_result : Result (26, 34739574800384) :=
  of_direct_small 26 34739574800384 (by decide) ⟨record010, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00085.record010.direct_core, record010_parameters, record010_coverage⟩
#print axioms record010_result

certified_graph_case record011 26 34746302791680 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10465 14

certified_graph_case record012 26 34746839597056 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10466 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085

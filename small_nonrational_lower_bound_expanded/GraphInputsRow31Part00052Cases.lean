module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00052Checked
public import GraphInputsRow31Part00052Metadata
public import GraphInputsRow31Part00052Frames
public import GraphInputsRow31Part00052Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch160
public import GraphInputsRow31Part00052Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00052
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 11151615213696 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16036 14

certified_graph_case record001 31 11214966030336 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16037 14

theorem record002_parameters : Parameters record002 (rowOfCode 31) 11223555932160 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 11223555932160 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16038 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 11223555932160
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch160.candidate16038_checked

theorem record002_result : Result (31, 11223555932160) :=
  of_direct_small 31 11223555932160 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00052.record002.direct_core, record002_parameters, record002_coverage⟩

certified_graph_case record003 31 11246782906368 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16039 14

theorem record004_parameters : Parameters record004 (rowOfCode 31) 11317654061056 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 11317654061056 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16040 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 11317654061056
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch160.candidate16040_checked

theorem record004_result : Result (31, 11317654061056) :=
  of_direct_small 31 11317654061056 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00052.record004.direct_core, record004_parameters, record004_coverage⟩

theorem record005_parameters : Parameters record005 (rowOfCode 31) 11364552704128 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 11364552704128 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16041 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 11364552704128
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch160.candidate16041_checked

theorem record005_result : Result (31, 11364552704128) :=
  of_direct_small 31 11364552704128 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00052.record005.direct_core, record005_parameters, record005_coverage⟩

certified_graph_case record006 31 11673993805824 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16042 14

certified_graph_case record007 31 11674530611200 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16043 14

certified_graph_case record008 31 11693451706368 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16044 14

certified_graph_case record009 31 11730369380352 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16045 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00052

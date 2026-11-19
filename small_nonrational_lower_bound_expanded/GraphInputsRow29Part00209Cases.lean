module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00209Checked
public import GraphInputsRow29Part00209Metadata
public import GraphInputsRow29Part00209Frames
public import GraphInputsRow29Part00209Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch119
public import GraphCoverageBatch154
public import GraphInputsRow29Part00209Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00209
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 29176267047040 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15414 14

theorem record001_parameters : Parameters record001 (rowOfCode 29) 29176518414464 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29176518414464 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11995 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 29176518414464
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch119.candidate11995_checked

theorem record001_result : Result (29, 29176518414464) :=
  of_direct_small 29 29176518414464 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00209.record001.direct_core, record001_parameters, record001_coverage⟩

certified_graph_case record002 29 29177059409920 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15415 14

theorem record003_parameters : Parameters record003 (rowOfCode 29) 29177591890560 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29177591890560 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11996 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 29177591890560
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch119.candidate11996_checked

theorem record003_result : Result (29, 29177591890560) :=
  of_direct_small 29 29177591890560 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00209.record003.direct_core, record003_parameters, record003_coverage⟩

certified_graph_case record004 29 29180303511552 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15416 14

certified_graph_case record005 29 29180410728704 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15417 14

certified_graph_case record006 29 29180561997952 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15418 14

certified_graph_case record007 29 29180567752704 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15419 14

certified_graph_case record008 29 29180679164032 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15420 14

theorem record009_parameters : Parameters record009 (rowOfCode 29) 29181484204800 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29181484204800 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15421 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 29181484204800
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.small_allowed record009 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch154.candidate15421_checked

theorem record009_result : Result (29, 29181484204800) :=
  of_direct_small 29 29181484204800 (by decide) ⟨record009, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00209.record009.direct_core, record009_parameters, record009_coverage⟩

certified_graph_case record010 29 29181752640128 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15422 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00209

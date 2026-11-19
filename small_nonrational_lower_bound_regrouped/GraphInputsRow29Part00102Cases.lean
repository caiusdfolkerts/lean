module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00102Checked
public import GraphInputsRow29Part00102Metadata
public import GraphInputsRow29Part00102Frames
public import GraphInputsRow29Part00102Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch115
public import GraphInputsRow29Part00102Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00102
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 17502528602112 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11519 14

theorem record001_parameters : Parameters record001 (rowOfCode 29) 17523487604736 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 17523487604736 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11520 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 17523487604736
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch115.candidate11520_checked

theorem record001_result : Result (29, 17523487604736) :=
  of_direct_small 29 17523487604736 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00102.record001.direct_core, record001_parameters, record001_coverage⟩
#print axioms record001_result

certified_graph_case record002 29 17532081668096 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11521 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00102

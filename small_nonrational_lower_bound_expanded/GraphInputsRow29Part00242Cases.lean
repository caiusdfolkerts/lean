module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00242Checked
public import GraphInputsRow29Part00242Metadata
public import GraphInputsRow29Part00242Frames
public import GraphInputsRow29Part00242Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch121
public import GraphInputsRow29Part00242Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00242
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 29) 31789477265408 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31789477265408 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12168 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 31789477265408
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch121.candidate12168_checked

theorem record000_result : Result (29, 31789477265408) :=
  of_direct_small 29 31789477265408 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00242.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 29 31790005747712 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12169 14

theorem record002_parameters : Parameters record002 (rowOfCode 29) 31795718389760 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31795718389760 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12170 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 31795718389760
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch121.candidate12170_checked

theorem record002_result : Result (29, 31795718389760) :=
  of_direct_small 29 31795718389760 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00242.record002.direct_core, record002_parameters, record002_coverage⟩

certified_graph_case record003 29 31812889870336 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12171 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00242

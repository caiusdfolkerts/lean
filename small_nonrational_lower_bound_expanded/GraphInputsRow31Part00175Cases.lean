module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00175Checked
public import GraphInputsRow31Part00175Metadata
public import GraphInputsRow31Part00175Frames
public import GraphInputsRow31Part00175Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch169
public import GraphInputsRow31Part00175Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00175
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 34651813449728 GraphCoverageDescriptions.GraphCoverageBatch169.candidate16919 14

certified_graph_case record001 31 34652870021120 GraphCoverageDescriptions.GraphCoverageBatch169.candidate16920 14

theorem record002_parameters : Parameters record002 (rowOfCode 31) 34660420157440 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34660420157440 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch169.candidate16921 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 34660420157440
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch169.candidate16921_checked

theorem record002_result : Result (31, 34660420157440) :=
  of_direct_small 31 34660420157440 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00175.record002.direct_core, record002_parameters, record002_coverage⟩

certified_graph_case record003 31 34704686317568 GraphCoverageDescriptions.GraphCoverageBatch169.candidate16922 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00175

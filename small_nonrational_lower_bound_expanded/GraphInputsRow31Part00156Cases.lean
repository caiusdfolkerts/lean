module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00156Checked
public import GraphInputsRow31Part00156Metadata
public import GraphInputsRow31Part00156Frames
public import GraphInputsRow31Part00156Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch167
public import GraphInputsRow31Part00156Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00156
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 30977862664192 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16789 14

certified_graph_case record001 31 30978259025920 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16790 14

certified_graph_case record002 31 30980405460992 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16791 14

certified_graph_case record003 31 30983963344896 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16792 14

certified_graph_case record004 31 31018322034688 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16793 14

theorem record005_parameters : Parameters record005 (rowOfCode 31) 31067680571648 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31067680571648 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16794 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 31067680571648
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch167.candidate16794_checked

theorem record005_result : Result (31, 31067680571648) :=
  of_direct_small 31 31067680571648 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00156.record005.direct_core, record005_parameters, record005_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00156

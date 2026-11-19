module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00159Checked
public import GraphInputsRow31Part00159Metadata
public import GraphInputsRow31Part00159Frames
public import GraphInputsRow31Part00159Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch168
public import GraphInputsRow31Part00159Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00159
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 31346316607488 GraphCoverageDescriptions.GraphCoverageBatch168.candidate16813 14

certified_graph_case record001 31 31354906509312 GraphCoverageDescriptions.GraphCoverageBatch168.candidate16814 14

certified_graph_case record002 31 31465207234560 GraphCoverageDescriptions.GraphCoverageBatch168.candidate16815 14

certified_graph_case record003 31 31465735716864 GraphCoverageDescriptions.GraphCoverageBatch168.candidate16816 14

certified_graph_case record004 31 31483796389888 GraphCoverageDescriptions.GraphCoverageBatch168.candidate16817 14

certified_graph_case record005 31 31490717524224 GraphCoverageDescriptions.GraphCoverageBatch168.candidate16818 14

theorem record006_parameters : Parameters record006 (rowOfCode 31) 31491254394880 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31491254394880 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch168.candidate16819 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 31491254394880
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch168.candidate16819_checked

theorem record006_result : Result (31, 31491254394880) :=
  of_direct_small 31 31491254394880 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00159.record006.direct_core, record006_parameters, record006_coverage⟩

certified_graph_case record007 31 31491774095616 GraphCoverageDescriptions.GraphCoverageBatch168.candidate16820 14

certified_graph_case record008 31 31492117889024 GraphCoverageDescriptions.GraphCoverageBatch168.candidate16821 14

certified_graph_case record009 31 31492377936384 GraphCoverageDescriptions.GraphCoverageBatch168.candidate16822 14

certified_graph_case record010 31 31492580311040 GraphCoverageDescriptions.GraphCoverageBatch168.candidate16823 14

theorem record011_parameters : Parameters record011 (rowOfCode 31) 31499324817408 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record011_coverage : Coverage record011 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31499324817408 :=
  GraphCoverageDescriptions.coverage_of_checked record011 GraphCoverageDescriptions.GraphCoverageBatch168.candidate16824 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 31499324817408
    (by rfl) record011_cells_exact
    (GraphCoverageDescriptions.small_allowed record011 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch168.candidate16824_checked

theorem record011_result : Result (31, 31499324817408) :=
  of_direct_small 31 31499324817408 (by decide) ⟨record011, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00159.record011.direct_core, record011_parameters, record011_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00159

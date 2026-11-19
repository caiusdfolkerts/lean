module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00127Checked
public import GraphInputsRow31Part00127Metadata
public import GraphInputsRow31Part00127Frames
public import GraphInputsRow31Part00127Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch166
public import GraphInputsRow31Part00127Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00127
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 28830106451968 GraphCoverageDescriptions.GraphCoverageBatch166.candidate16659 14

certified_graph_case record001 31 28834539765760 GraphCoverageDescriptions.GraphCoverageBatch166.candidate16660 14

certified_graph_case record002 31 28835068248064 GraphCoverageDescriptions.GraphCoverageBatch166.candidate16661 14

certified_graph_case record003 31 28847286255616 GraphCoverageDescriptions.GraphCoverageBatch166.candidate16662 14

certified_graph_case record004 31 28871055908928 GraphCoverageDescriptions.GraphCoverageBatch166.candidate16663 14

certified_graph_case record005 31 28875099750528 GraphCoverageDescriptions.GraphCoverageBatch166.candidate16664 14

certified_graph_case record006 31 28875468316672 GraphCoverageDescriptions.GraphCoverageBatch166.candidate16665 14

theorem record007_parameters : Parameters record007 (rowOfCode 31) 28898823798912 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 28898823798912 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch166.candidate16666 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 28898823798912
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch166.candidate16666_checked

theorem record007_result : Result (31, 28898823798912) :=
  of_direct_small 31 28898823798912 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00127.record007.direct_core, record007_parameters, record007_coverage⟩

theorem record008_parameters : Parameters record008 (rowOfCode 31) 28967545372672 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 28967545372672 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch166.candidate16667 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 28967545372672
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch166.candidate16667_checked

theorem record008_result : Result (31, 28967545372672) :=
  of_direct_small 31 28967545372672 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00127.record008.direct_core, record008_parameters, record008_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00127

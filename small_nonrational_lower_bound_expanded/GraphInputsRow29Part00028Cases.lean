module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00028Checked
public import GraphInputsRow29Part00028Metadata
public import GraphInputsRow29Part00028Frames
public import GraphInputsRow29Part00028Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch108
public import GraphCoverageBatch144
public import GraphInputsRow29Part00028Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00028
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 6807055532288 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10845 14

certified_graph_case record001 29 6823834877952 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10846 14

certified_graph_case record002 29 6825520930816 GraphCoverageDescriptions.GraphCoverageBatch144.candidate14418 14

certified_graph_case record003 29 6839890673920 GraphCoverageDescriptions.GraphCoverageBatch144.candidate14419 14

certified_graph_case record004 29 6839899062272 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10847 14

certified_graph_case record005 29 6840138400000 GraphCoverageDescriptions.GraphCoverageBatch144.candidate14420 14

certified_graph_case record006 29 6840291197184 GraphCoverageDescriptions.GraphCoverageBatch144.candidate14421 14

certified_graph_case record007 29 6840295424000 GraphCoverageDescriptions.GraphCoverageBatch144.candidate14422 14

theorem record008_parameters : Parameters record008 (rowOfCode 29) 6840406802688 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 6840406802688 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10848 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 6840406802688
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch108.candidate10848_checked

theorem record008_result : Result (29, 6840406802688) :=
  of_direct_small 29 6840406802688 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00028.record008.direct_core, record008_parameters, record008_coverage⟩

theorem record009_parameters : Parameters record009 (rowOfCode 29) 6840419092480 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 6840419092480 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10849 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 6840419092480
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.small_allowed record009 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch108.candidate10849_checked

theorem record009_result : Result (29, 6840419092480) :=
  of_direct_small 29 6840419092480 (by decide) ⟨record009, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00028.record009.direct_core, record009_parameters, record009_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00028

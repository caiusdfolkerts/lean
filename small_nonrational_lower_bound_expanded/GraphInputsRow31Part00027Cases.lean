module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00027Checked
public import GraphInputsRow31Part00027Metadata
public import GraphInputsRow31Part00027Frames
public import GraphInputsRow31Part00027Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch158
public import GraphInputsRow31Part00027Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00027
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 6706864128256 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15853 14

certified_graph_case record001 31 6707400998912 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15854 14

certified_graph_case record002 31 6707409321984 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15855 14

certified_graph_case record003 31 6711561748480 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15856 14

certified_graph_case record004 31 6711570071552 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15857 14

theorem record005_parameters : Parameters record005 (rowOfCode 31) 6713642123264 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 6713642123264 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15858 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 6713642123264
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch158.candidate15858_checked

theorem record005_result : Result (31, 6713642123264) :=
  of_direct_small 31 6713642123264 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00027.record005.direct_core, record005_parameters, record005_coverage⟩

certified_graph_case record006 31 6743661224000 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15859 14

certified_graph_case record007 31 6744717795392 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15860 14

certified_graph_case record008 31 6825508340256 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15861 14

theorem record009_parameters : Parameters record009 (rowOfCode 31) 6844307275776 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 6844307275776 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15862 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 6844307275776
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.small_allowed record009 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch158.candidate15862_checked

theorem record009_result : Result (31, 6844307275776) :=
  of_direct_small 31 6844307275776 (by decide) ⟨record009, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00027.record009.direct_core, record009_parameters, record009_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00027

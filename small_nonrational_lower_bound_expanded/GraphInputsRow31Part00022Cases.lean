module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00022Checked
public import GraphInputsRow31Part00022Metadata
public import GraphInputsRow31Part00022Frames
public import GraphInputsRow31Part00022Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch157
public import GraphCoverageBatch158
public import GraphInputsRow31Part00022Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00022
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 5279324372992 GraphCoverageDescriptions.GraphCoverageBatch157.candidate15795 14

certified_graph_case record001 31 5279332696064 GraphCoverageDescriptions.GraphCoverageBatch157.candidate15796 14

certified_graph_case record002 31 5317240881408 GraphCoverageDescriptions.GraphCoverageBatch157.candidate15797 14

certified_graph_case record003 31 5317974819360 GraphCoverageDescriptions.GraphCoverageBatch157.candidate15798 14

certified_graph_case record004 31 5317975932928 GraphCoverageDescriptions.GraphCoverageBatch157.candidate15799 14

certified_graph_case record005 31 5413944754176 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15800 14

certified_graph_case record006 31 5516394766400 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15801 14

theorem record007_parameters : Parameters record007 (rowOfCode 31) 5572262952960 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 5572262952960 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15802 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 5572262952960
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch158.candidate15802_checked

theorem record007_result : Result (31, 5572262952960) :=
  of_direct_small 31 5572262952960 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00022.record007.direct_core, record007_parameters, record007_coverage⟩

theorem record008_parameters : Parameters record008 (rowOfCode 31) 5572452745472 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 5572452745472 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15803 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 5572452745472
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch158.candidate15803_checked

theorem record008_result : Result (31, 5572452745472) :=
  of_direct_small 31 5572452745472 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00022.record008.direct_core, record008_parameters, record008_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00022

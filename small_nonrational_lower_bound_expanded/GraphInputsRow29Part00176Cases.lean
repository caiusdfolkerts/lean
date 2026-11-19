module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00176Checked
public import GraphInputsRow29Part00176Metadata
public import GraphInputsRow29Part00176Frames
public import GraphInputsRow29Part00176Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch118
public import GraphCoverageBatch152
public import GraphInputsRow29Part00176Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00176
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 29) 25857582710784 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25857582710784 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11870 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25857582710784
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch118.candidate11870_checked

theorem record000_result : Result (29, 25857582710784) :=
  of_direct_small 29 25857582710784 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00176.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 29 25860032200960 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15274 14

certified_graph_case record002 29 25860803923968 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11871 14

certified_graph_case record003 29 25864327151872 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11872 14

certified_graph_case record004 29 25912888328192 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15275 14

certified_graph_case record005 29 25915850031360 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15276 14

certified_graph_case record006 29 25916386902016 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15277 14

theorem record007_parameters : Parameters record007 (rowOfCode 29) 25916395225088 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25916395225088 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11873 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25916395225088
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch118.candidate11873_checked

theorem record007_result : Result (29, 25916395225088) :=
  of_direct_small 29 25916395225088 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00176.record007.direct_core, record007_parameters, record007_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00176

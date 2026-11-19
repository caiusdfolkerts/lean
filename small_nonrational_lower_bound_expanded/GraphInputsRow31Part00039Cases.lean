module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00039Checked
public import GraphInputsRow31Part00039Metadata
public import GraphInputsRow31Part00039Frames
public import GraphInputsRow31Part00039Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch159
public import GraphInputsRow31Part00039Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00039
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 31) 7771277819904 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 7771277819904 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15930 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 7771277819904
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch159.candidate15930_checked

theorem record000_result : Result (31, 7771277819904) :=
  of_direct_small 31 7771277819904 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00039.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 31 7771781136640 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15931 14

certified_graph_case record002 31 7783760068608 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15932 14

certified_graph_case record003 31 7821135610112 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15933 14

certified_graph_case record004 31 7821412335616 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15934 14

certified_graph_case record005 31 8027969159168 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15935 14

certified_graph_case record006 31 8045891420160 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15936 14

certified_graph_case record007 31 8134668206336 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15937 14

theorem record008_parameters : Parameters record008 (rowOfCode 31) 8251743731968 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8251743731968 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15938 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8251743731968
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch159.candidate15938_checked

theorem record008_result : Result (31, 8251743731968) :=
  of_direct_small 31 8251743731968 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00039.record008.direct_core, record008_parameters, record008_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00039

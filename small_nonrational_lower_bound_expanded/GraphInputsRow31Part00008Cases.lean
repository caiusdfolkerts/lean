module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00008Checked
public import GraphInputsRow31Part00008Metadata
public import GraphInputsRow31Part00008Frames
public import GraphInputsRow31Part00008Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch156
public import GraphInputsRow31Part00008Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00008
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 1393058390080 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15650 14

certified_graph_case record001 31 1422317846529 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15651 14

certified_graph_case record002 31 1430907813888 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15652 14

certified_graph_case record003 31 1431031546112 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15653 14

certified_graph_case record004 31 1431042015232 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15654 14

certified_graph_case record005 31 1435326497024 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15655 14

certified_graph_case record006 31 1469685186816 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15656 14

certified_graph_case record007 31 1765508448512 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15657 14

theorem record008_parameters : Parameters record008 (rowOfCode 31) 1766045319168 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 1766045319168 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15658 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 1766045319168
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch156.candidate15658_checked

theorem record008_result : Result (31, 1766045319168) :=
  of_direct_small 31 1766045319168 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00008.record008.direct_core, record008_parameters, record008_coverage⟩

theorem record009_parameters : Parameters record009 (rowOfCode 31) 1774094188800 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 1774094188800 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15659 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 1774094188800
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.small_allowed record009 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch156.candidate15659_checked

theorem record009_result : Result (31, 1774094188800) :=
  of_direct_small 31 1774094188800 (by decide) ⟨record009, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00008.record009.direct_core, record009_parameters, record009_coverage⟩

theorem record010_parameters : Parameters record010 (rowOfCode 31) 1774631059456 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record010_coverage : Coverage record010 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 1774631059456 :=
  GraphCoverageDescriptions.coverage_of_checked record010 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15660 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 1774631059456
    (by rfl) record010_cells_exact
    (GraphCoverageDescriptions.small_allowed record010 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch156.candidate15660_checked

theorem record010_result : Result (31, 1774631059456) :=
  of_direct_small 31 1774631059456 (by decide) ⟨record010, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00008.record010.direct_core, record010_parameters, record010_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00008

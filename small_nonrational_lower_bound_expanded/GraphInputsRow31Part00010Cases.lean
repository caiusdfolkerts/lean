module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00010Checked
public import GraphInputsRow31Part00010Metadata
public import GraphInputsRow31Part00010Frames
public import GraphInputsRow31Part00010Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch156
public import GraphInputsRow31Part00010Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 1972073660416 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15680 14

certified_graph_case record001 31 2015149228032 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15681 14

certified_graph_case record002 31 2015157551104 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15682 14

theorem record003_parameters : Parameters record003 (rowOfCode 31) 2018703868160 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 2018703868160 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15683 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 2018703868160
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch156.candidate15683_checked

theorem record003_result : Result (31, 2018703868160) :=
  of_direct_small 31 2018703868160 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00010.record003.direct_core, record003_parameters, record003_coverage⟩

certified_graph_case record004 31 2018773106944 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15684 14

certified_graph_case record005 31 2019439936256 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15685 14

certified_graph_case record006 31 2019444195328 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15686 14

certified_graph_case record007 31 2019452518400 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15687 14

theorem record008_parameters : Parameters record008 (rowOfCode 31) 2031792226560 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 2031792226560 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15688 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 2031792226560
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch156.candidate15688_checked

theorem record008_result : Result (31, 2031792226560) :=
  of_direct_small 31 2031792226560 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00010.record008.direct_core, record008_parameters, record008_coverage⟩

certified_graph_case record009 31 2040386355200 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15689 14

certified_graph_case record010 31 2040923160576 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15690 14

certified_graph_case record011 31 2053132845056 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15691 14

certified_graph_case record012 31 2057566158848 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15692 14

certified_graph_case record013 31 2058094641152 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15693 14

certified_graph_case record014 31 2087492583680 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15694 14

certified_graph_case record015 31 2088161574912 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15695 14

certified_graph_case record016 31 2132589740288 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15696 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00010

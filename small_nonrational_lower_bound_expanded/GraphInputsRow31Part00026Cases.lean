module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00026Checked
public import GraphInputsRow31Part00026Metadata
public import GraphInputsRow31Part00026Frames
public import GraphInputsRow31Part00026Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch158
public import GraphInputsRow31Part00026Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00026
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 6379905482752 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15839 14

certified_graph_case record001 31 6417494835200 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15840 14

certified_graph_case record002 31 6425292112128 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15841 14

certified_graph_case record003 31 6433886240768 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15842 14

certified_graph_case record004 31 6434423046144 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15843 14

certified_graph_case record005 31 6442471981056 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15844 14

certified_graph_case record006 31 6443256512512 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15845 14

certified_graph_case record007 31 6451041075200 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15846 14

certified_graph_case record008 31 6451586138112 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15847 14

certified_graph_case record009 31 6607316459584 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15848 14

certified_graph_case record010 31 6671975849984 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15849 14

certified_graph_case record011 31 6676136599552 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15850 14

certified_graph_case record012 31 6684446589184 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15851 14

theorem record013_parameters : Parameters record013 (rowOfCode 31) 6684458098688 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record013_coverage : Coverage record013 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 6684458098688 :=
  GraphCoverageDescriptions.coverage_of_checked record013 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15852 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 6684458098688
    (by rfl) record013_cells_exact
    (GraphCoverageDescriptions.small_allowed record013 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch158.candidate15852_checked

theorem record013_result : Result (31, 6684458098688) :=
  of_direct_small 31 6684458098688 (by decide) ⟨record013, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00026.record013.direct_core, record013_parameters, record013_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00026

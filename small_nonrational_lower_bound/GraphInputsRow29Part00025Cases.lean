module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00025Checked
public import GraphInputsRow29Part00025Metadata
public import GraphInputsRow29Part00025Frames
public import GraphInputsRow29Part00025Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch108
public import GraphCoverageBatch144
public import GraphInputsRow29Part00025Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 6413204062208 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10818 14

theorem record001_parameters : Parameters record001 (rowOfCode 29) 6425556615424 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 6425556615424 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch144.candidate14406 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 6425556615424
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch144.candidate14406_checked

theorem record001_result : Result (29, 6425556615424) :=
  of_direct_small 29 6425556615424 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00025.record001.direct_core, record001_parameters, record001_coverage⟩
#print axioms record001_result

certified_graph_case record002 29 6425565003776 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10819 14

certified_graph_case record003 29 6425825018112 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10820 14

certified_graph_case record004 29 6425837307904 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10821 14

certified_graph_case record005 29 6426076645632 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10822 14

certified_graph_case record006 29 6434398013696 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10823 14

certified_graph_case record007 29 6434406402048 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10824 14

theorem record008_parameters : Parameters record008 (rowOfCode 29) 6434414658304 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 6434414658304 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10825 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 6434414658304
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch108.candidate10825_checked

theorem record008_result : Result (29, 6434414658304) :=
  of_direct_small 29 6434414658304 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00025.record008.direct_core, record008_parameters, record008_coverage⟩
#print axioms record008_result

certified_graph_case record009 29 6442727901184 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10826 14

certified_graph_case record010 29 6443017175040 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10827 14

certified_graph_case record011 29 6443256250888 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10828 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00025

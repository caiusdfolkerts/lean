module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00109Checked
public import GraphInputsRow29Part00109Metadata
public import GraphInputsRow29Part00109Frames
public import GraphInputsRow29Part00109Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch115
public import GraphCoverageBatch148
public import GraphInputsRow29Part00109Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00109
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 18543793995776 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14867 14

theorem record001_parameters : Parameters record001 (rowOfCode 29) 18544330801152 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 18544330801152 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11559 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 18544330801152
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch115.candidate11559_checked

theorem record001_result : Result (29, 18544330801152) :=
  of_direct_small 29 18544330801152 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00109.record001.direct_core, record001_parameters, record001_coverage⟩

certified_graph_case record002 29 18545738023168 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14868 14

certified_graph_case record003 29 18548491550720 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11560 14

certified_graph_case record004 29 18593115046144 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11561 14

certified_graph_case record005 29 18595736256512 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14869 14

certified_graph_case record006 29 18731637965056 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14870 14

certified_graph_case record007 29 18778875265280 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11562 14

certified_graph_case record008 29 18779352342656 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14871 14

certified_graph_case record009 29 18779488657472 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14872 14

certified_graph_case record010 29 18801894686976 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14873 14

certified_graph_case record011 29 18814785847296 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14874 14

theorem record012_parameters : Parameters record012 (rowOfCode 29) 18817531052032 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record012_coverage : Coverage record012 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 18817531052032 :=
  GraphCoverageDescriptions.coverage_of_checked record012 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11563 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 18817531052032
    (by rfl) record012_cells_exact
    (GraphCoverageDescriptions.small_allowed record012 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch115.candidate11563_checked

theorem record012_result : Result (29, 18817531052032) :=
  of_direct_small 29 18817531052032 (by decide) ⟨record012, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00109.record012.direct_core, record012_parameters, record012_coverage⟩

certified_graph_case record013 29 18839414784256 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14875 14

certified_graph_case record014 29 18839414849536 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14876 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00109

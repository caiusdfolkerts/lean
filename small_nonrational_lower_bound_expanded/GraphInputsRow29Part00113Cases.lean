module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00113Checked
public import GraphInputsRow29Part00113Metadata
public import GraphInputsRow29Part00113Frames
public import GraphInputsRow29Part00113Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch115
public import GraphCoverageBatch149
public import GraphInputsRow29Part00113Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00113
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 19592068005888 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14918 14

certified_graph_case record001 29 19610889912576 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14919 14

certified_graph_case record002 29 19611625980480 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11575 14

certified_graph_case record003 29 19611627044864 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11576 14

certified_graph_case record004 29 19619561898240 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14920 14

theorem record005_parameters : Parameters record005 (rowOfCode 29) 19619574188032 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 19619574188032 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11577 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 19619574188032
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch115.candidate11577_checked

theorem record005_result : Result (29, 19619574188032) :=
  of_direct_small 29 19619574188032 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00113.record005.direct_core, record005_parameters, record005_coverage⟩

certified_graph_case record006 29 19623978270976 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14921 14

theorem record007_parameters : Parameters record007 (rowOfCode 29) 19623982532608 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 19623982532608 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11578 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 19623982532608
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch115.candidate11578_checked

theorem record007_result : Result (29, 19623982532608) :=
  of_direct_small 29 19623982532608 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00113.record007.direct_core, record007_parameters, record007_coverage⟩

certified_graph_case record008 29 19624263483392 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14922 14

theorem record009_parameters : Parameters record009 (rowOfCode 29) 19624510882312 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 19624510882312 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11579 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 19624510882312
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.small_allowed record009 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch115.candidate11579_checked

theorem record009_result : Result (29, 19624510882312) :=
  of_direct_small 29 19624510882312 (by decide) ⟨record009, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00113.record009.direct_core, record009_parameters, record009_coverage⟩

certified_graph_case record010 29 19632572399616 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14923 14

certified_graph_case record011 29 19633109204992 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11580 14

certified_graph_case record012 29 19637261860864 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11581 14

certified_graph_case record013 29 19645318889472 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14924 14

certified_graph_case record014 29 19645987815424 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11582 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00113

module
prelude
public meta import GraphCases
public import GraphInputsRow23Part00027Checked
public import GraphInputsRow23Part00027Metadata
public import GraphInputsRow23Part00027Frames
public import GraphInputsRow23Part00027Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch059
public import GraphInputsRow23Part00027Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00027
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 23 32172057051136 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05969 6

theorem record001_parameters : Parameters record001 (rowOfCode 23) 32198434553856 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32198434553856 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05970 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 32198434553856
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch059.candidate05970_checked

theorem record001_result : Result (23, 32198434553856) :=
  of_direct_small 23 32198434553856 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00027.record001.direct_core, record001_parameters, record001_coverage⟩

certified_graph_case record002 23 32199103479808 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05971 6

certified_graph_case record003 23 32205344604160 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05972 6

theorem record004_parameters : Parameters record004 (rowOfCode 23) 32270513602560 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32270513602560 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05973 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 32270513602560
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch059.candidate05973_checked

theorem record004_result : Result (23, 32270513602560) :=
  of_direct_small 23 32270513602560 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00027.record004.direct_core, record004_parameters, record004_coverage⟩

certified_graph_case record005 23 32271042084864 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05974 6

certified_graph_case record006 23 32301981368320 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05975 6

certified_graph_case record007 23 32334680227840 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05976 6

theorem record008_parameters : Parameters record008 (rowOfCode 23) 32335217033216 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32335217033216 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05977 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 32335217033216
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch059.candidate05977_checked

theorem record008_result : Result (23, 32335217033216) :=
  of_direct_small 23 32335217033216 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00027.record008.direct_core, record008_parameters, record008_coverage⟩

certified_graph_case record009 23 32351841304576 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05978 6

certified_graph_case record010 23 32475598356480 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05979 6

certified_graph_case record011 23 32476135161856 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05980 6

theorem record012_parameters : Parameters record012 (rowOfCode 23) 32488344846336 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record012_coverage : Coverage record012 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32488344846336 :=
  GraphCoverageDescriptions.coverage_of_checked record012 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05981 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 32488344846336
    (by rfl) record012_cells_exact
    (GraphCoverageDescriptions.small_allowed record012 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch059.candidate05981_checked

theorem record012_result : Result (23, 32488344846336) :=
  of_direct_small 23 32488344846336 (by decide) ⟨record012, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00027.record012.direct_core, record012_parameters, record012_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00027

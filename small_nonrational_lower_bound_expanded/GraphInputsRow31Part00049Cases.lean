module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00049Checked
public import GraphInputsRow31Part00049Metadata
public import GraphInputsRow31Part00049Frames
public import GraphInputsRow31Part00049Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch160
public import GraphInputsRow31Part00049Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00049
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 10183770644736 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16015 14

certified_graph_case record001 31 10218129851136 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16016 14

theorem record002_parameters : Parameters record002 (rowOfCode 31) 10218410868736 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10218410868736 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16017 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10218410868736
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch160.candidate16017_checked

theorem record002_result : Result (31, 10218410868736) :=
  of_direct_small 31 10218410868736 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00049.record002.direct_core, record002_parameters, record002_coverage⟩

certified_graph_case record003 31 10227124568064 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16018 14

certified_graph_case record004 31 10231417406016 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16019 14

theorem record005_parameters : Parameters record005 (rowOfCode 31) 10261483257856 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10261483257856 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16020 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10261483257856
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch160.candidate16020_checked

theorem record005_result : Result (31, 10261483257856) :=
  of_direct_small 31 10261483257856 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00049.record005.direct_core, record005_parameters, record005_coverage⟩

certified_graph_case record006 31 10489794985984 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16021 14

theorem record007_parameters : Parameters record007 (rowOfCode 31) 10490059227136 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10490059227136 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16022 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10490059227136
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch160.candidate16022_checked

theorem record007_result : Result (31, 10490059227136) :=
  of_direct_small 31 10490059227136 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00049.record007.direct_core, record007_parameters, record007_coverage⟩

theorem record008_parameters : Parameters record008 (rowOfCode 31) 10490067550208 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10490067550208 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16023 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10490067550208
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch160.candidate16023_checked

theorem record008_result : Result (31, 10490067550208) :=
  of_direct_small 31 10490067550208 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00049.record008.direct_core, record008_parameters, record008_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00049

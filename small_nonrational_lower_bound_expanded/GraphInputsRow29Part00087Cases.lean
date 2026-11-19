module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00087Checked
public import GraphInputsRow29Part00087Metadata
public import GraphInputsRow29Part00087Frames
public import GraphInputsRow29Part00087Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch113
public import GraphCoverageBatch147
public import GraphInputsRow29Part00087Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00087
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 14768916135936 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11358 14

certified_graph_case record001 29 14972532883456 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14712 14

certified_graph_case record002 29 14973069688832 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14713 14

theorem record003_parameters : Parameters record003 (rowOfCode 29) 15037494198272 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 15037494198272 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11359 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 15037494198272
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch113.candidate11359_checked

theorem record003_result : Result (29, 15037494198272) :=
  of_direct_small 29 15037494198272 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00087.record003.direct_core, record003_parameters, record003_coverage⟩

certified_graph_case record004 29 15075335405824 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14714 14

certified_graph_case record005 29 15075410771968 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14715 14

certified_graph_case record006 29 15110240206848 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14716 14

certified_graph_case record007 29 15166343217152 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14717 14

theorem record008_parameters : Parameters record008 (rowOfCode 29) 15178552901632 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 15178552901632 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14718 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 15178552901632
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch147.candidate14718_checked

theorem record008_result : Result (29, 15178552901632) :=
  of_direct_small 29 15178552901632 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00087.record008.direct_core, record008_parameters, record008_coverage⟩

certified_graph_case record009 29 15212845531136 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11360 14

certified_graph_case record010 29 15213580517376 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11361 14

certified_graph_case record011 29 15247410724864 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11362 14

certified_graph_case record012 29 15258009796864 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14719 14

certified_graph_case record013 29 15294655430656 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14720 14

certified_graph_case record014 29 15303513735168 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14721 14

theorem record015_parameters : Parameters record015 (rowOfCode 29) 15311835234304 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record015_coverage : Coverage record015 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 15311835234304 :=
  GraphCoverageDescriptions.coverage_of_checked record015 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11363 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 15311835234304
    (by rfl) record015_cells_exact
    (GraphCoverageDescriptions.small_allowed record015 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch113.candidate11363_checked

theorem record015_result : Result (29, 15311835234304) :=
  of_direct_small 29 15311835234304 (by decide) ⟨record015, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00087.record015.direct_core, record015_parameters, record015_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00087

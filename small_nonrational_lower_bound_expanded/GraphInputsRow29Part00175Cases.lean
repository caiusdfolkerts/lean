module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00175Checked
public import GraphInputsRow29Part00175Metadata
public import GraphInputsRow29Part00175Frames
public import GraphInputsRow29Part00175Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch118
public import GraphCoverageBatch152
public import GraphInputsRow29Part00175Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00175
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 25844697858048 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11866 14

certified_graph_case record001 29 25848222646528 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15269 14

theorem record002_parameters : Parameters record002 (rowOfCode 29) 25848759517184 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25848759517184 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11867 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25848759517184
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch118.candidate11867_checked

theorem record002_result : Result (29, 25848759517184) :=
  of_direct_small 29 25848759517184 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00175.record002.direct_core, record002_parameters, record002_coverage⟩

theorem record003_parameters : Parameters record003 (rowOfCode 29) 25848767840256 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25848767840256 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11868 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25848767840256
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch118.candidate11868_checked

theorem record003_result : Result (29, 25848767840256) :=
  of_direct_small 29 25848767840256 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00175.record003.direct_core, record003_parameters, record003_coverage⟩

certified_graph_case record004 29 25848858607616 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15270 14

certified_graph_case record005 29 25851442299136 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15271 14

theorem record006_parameters : Parameters record006 (rowOfCode 29) 25856812548352 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25856812548352 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15272 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25856812548352
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch152.candidate15272_checked

theorem record006_result : Result (29, 25856812548352) :=
  of_direct_small 29 25856812548352 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00175.record006.direct_core, record006_parameters, record006_coverage⟩

theorem record007_parameters : Parameters record007 (rowOfCode 29) 25857180106752 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25857180106752 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15273 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25857180106752
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch152.candidate15273_checked

theorem record007_result : Result (29, 25857180106752) :=
  of_direct_small 29 25857180106752 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00175.record007.direct_core, record007_parameters, record007_coverage⟩

certified_graph_case record008 29 25857353580544 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11869 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00175

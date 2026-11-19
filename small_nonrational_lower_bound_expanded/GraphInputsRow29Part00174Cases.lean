module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00174Checked
public import GraphInputsRow29Part00174Metadata
public import GraphInputsRow29Part00174Frames
public import GraphInputsRow29Part00174Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch118
public import GraphCoverageBatch152
public import GraphInputsRow29Part00174Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00174
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 29) 25789131276288 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25789131276288 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11864 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25789131276288
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch118.candidate11864_checked

theorem record000_result : Result (29, 25789131276288) :=
  of_direct_small 29 25789131276288 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00174.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 29 25843929776384 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15266 14

certified_graph_case record002 29 25844202405888 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15267 14

theorem record003_parameters : Parameters record003 (rowOfCode 29) 25844466647040 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25844466647040 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15268 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25844466647040
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch152.candidate15268_checked

theorem record003_result : Result (29, 25844466647040) :=
  of_direct_small 29 25844466647040 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00174.record003.direct_core, record003_parameters, record003_coverage⟩

theorem record004_parameters : Parameters record004 (rowOfCode 29) 25844474970112 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25844474970112 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11865 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25844474970112
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch118.candidate11865_checked

theorem record004_result : Result (29, 25844474970112) :=
  of_direct_small 29 25844474970112 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00174.record004.direct_core, record004_parameters, record004_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00174

module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00183Checked
public import GraphInputsRow29Part00183Metadata
public import GraphInputsRow29Part00183Frames
public import GraphInputsRow29Part00183Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch119
public import GraphCoverageBatch153
public import GraphInputsRow29Part00183Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00183
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 26571622596864 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15327 14

certified_graph_case record001 29 26648730697728 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11905 14

certified_graph_case record002 29 26670014664736 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15328 14

theorem record003_parameters : Parameters record003 (rowOfCode 29) 26777579716608 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 26777579716608 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11906 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 26777579716608
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch119.candidate11906_checked

theorem record003_result : Result (29, 26777579716608) :=
  of_direct_small 29 26777579716608 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00183.record003.direct_core, record003_parameters, record003_coverage⟩

certified_graph_case record004 29 26943718170880 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15329 14

theorem record005_parameters : Parameters record005 (rowOfCode 29) 26943986606208 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 26943986606208 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11907 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 26943986606208
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch119.candidate11907_checked

theorem record005_result : Result (29, 26943986606208) :=
  of_direct_small 29 26943986606208 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00183.record005.direct_core, record005_parameters, record005_coverage⟩

certified_graph_case record006 29 26948279476352 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15330 14

certified_graph_case record007 29 26956865216640 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15331 14

theorem record008_parameters : Parameters record008 (rowOfCode 29) 26990985904384 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 26990985904384 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15332 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 26990985904384
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch153.candidate15332_checked

theorem record008_result : Result (29, 26990985904384) :=
  of_direct_small 29 26990985904384 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00183.record008.direct_core, record008_parameters, record008_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00183

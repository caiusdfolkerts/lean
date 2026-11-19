module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00083Checked
public import GraphInputsRow29Part00083Metadata
public import GraphInputsRow29Part00083Frames
public import GraphInputsRow29Part00083Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch113
public import GraphCoverageBatch146
public import GraphInputsRow29Part00083Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 29) 13752779477024 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 13752779477024 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11324 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 13752779477024
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch113.candidate11324_checked

theorem record000_result : Result (29, 13752779477024) :=
  of_direct_small 29 13752779477024 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00083.record000.direct_core, record000_parameters, record000_coverage⟩

theorem record001_parameters : Parameters record001 (rowOfCode 29) 13753043718176 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 13753043718176 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11325 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 13753043718176
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch113.candidate11325_checked

theorem record001_result : Result (29, 13753043718176) :=
  of_direct_small 29 13753043718176 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00083.record001.direct_core, record001_parameters, record001_coverage⟩

certified_graph_case record002 29 13754142040320 GraphCoverageDescriptions.GraphCoverageBatch146.candidate14686 14

theorem record003_parameters : Parameters record003 (rowOfCode 29) 13762731974784 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 13762731974784 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11326 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 13762731974784
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch113.candidate11326_checked

theorem record003_result : Result (29, 13762731974784) :=
  of_direct_small 29 13762731974784 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00083.record003.direct_core, record003_parameters, record003_coverage⟩

certified_graph_case record004 29 13890486804736 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11327 14

theorem record005_parameters : Parameters record005 (rowOfCode 29) 13890486870016 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 13890486870016 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11328 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 13890486870016
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch113.candidate11328_checked

theorem record005_result : Result (29, 13890486870016) :=
  of_direct_small 29 13890486870016 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00083.record005.direct_core, record005_parameters, record005_coverage⟩

certified_graph_case record006 29 13899076739200 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11329 14

certified_graph_case record007 29 13899080405024 GraphCoverageDescriptions.GraphCoverageBatch146.candidate14687 14

certified_graph_case record008 29 13899936104448 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11330 14

certified_graph_case record009 29 13900204474369 GraphCoverageDescriptions.GraphCoverageBatch146.candidate14688 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083

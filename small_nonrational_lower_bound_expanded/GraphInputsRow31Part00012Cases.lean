module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00012Checked
public import GraphInputsRow31Part00012Metadata
public import GraphInputsRow31Part00012Frames
public import GraphInputsRow31Part00012Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch157
public import GraphInputsRow31Part00012Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00012
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 2418470355200 GraphCoverageDescriptions.GraphCoverageBatch157.candidate15701 14

certified_graph_case record001 31 2521554812928 GraphCoverageDescriptions.GraphCoverageBatch157.candidate15702 14

certified_graph_case record002 31 2530543173760 GraphCoverageDescriptions.GraphCoverageBatch157.candidate15703 14

certified_graph_case record003 31 2534838124672 GraphCoverageDescriptions.GraphCoverageBatch157.candidate15704 14

certified_graph_case record004 31 2569196814464 GraphCoverageDescriptions.GraphCoverageBatch157.candidate15705 14

certified_graph_case record005 31 2637916291136 GraphCoverageDescriptions.GraphCoverageBatch157.candidate15706 14

theorem record006_parameters : Parameters record006 (rowOfCode 31) 2933601140992 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 2933601140992 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch157.candidate15707 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 2933601140992
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch157.candidate15707_checked

theorem record006_result : Result (31, 2933601140992) :=
  of_direct_small 31 2933601140992 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00012.record006.direct_core, record006_parameters, record006_coverage⟩

theorem record007_parameters : Parameters record007 (rowOfCode 31) 2933873770496 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 2933873770496 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch157.candidate15708 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 2933873770496
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch157.candidate15708_checked

theorem record007_result : Result (31, 2933873770496) :=
  of_direct_small 31 2933873770496 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00012.record007.direct_core, record007_parameters, record007_coverage⟩

certified_graph_case record008 31 3118284701952 GraphCoverageDescriptions.GraphCoverageBatch157.candidate15709 14

certified_graph_case record009 31 3118951563904 GraphCoverageDescriptions.GraphCoverageBatch157.candidate15710 14

certified_graph_case record010 31 3118953693184 GraphCoverageDescriptions.GraphCoverageBatch157.candidate15711 14

certified_graph_case record011 31 3187671040576 GraphCoverageDescriptions.GraphCoverageBatch157.candidate15712 14

certified_graph_case record012 31 3208751611904 GraphCoverageDescriptions.GraphCoverageBatch157.candidate15713 14

theorem record013_parameters : Parameters record013 (rowOfCode 31) 3240963866624 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record013_coverage : Coverage record013 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 3240963866624 :=
  GraphCoverageDescriptions.coverage_of_checked record013 GraphCoverageDescriptions.GraphCoverageBatch157.candidate15714 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 3240963866624
    (by rfl) record013_cells_exact
    (GraphCoverageDescriptions.small_allowed record013 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch157.candidate15714_checked

theorem record013_result : Result (31, 3240963866624) :=
  of_direct_small 31 3240963866624 (by decide) ⟨record013, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00012.record013.direct_core, record013_parameters, record013_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00012

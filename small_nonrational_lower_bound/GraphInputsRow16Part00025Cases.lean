module
prelude
public meta import GraphCases
public import GraphInputsRow16Part00025Checked
public import GraphInputsRow16Part00025Metadata
public import GraphInputsRow16Part00025Frames
public import GraphInputsRow16Part00025Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch014
public import GraphCoverageBatch015
public import GraphInputsRow16Part00025Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 16 25260850315520 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01496 14

certified_graph_case record001 16 25260871188480 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01497 14

certified_graph_case record002 16 25261143752704 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01498 14

certified_graph_case record003 16 25261655458304 GraphCoverageDescriptions.GraphCoverageBatch014.candidate01499 14

certified_graph_case record004 16 25261655719936 GraphCoverageDescriptions.GraphCoverageBatch015.candidate01500 14

certified_graph_case record005 16 25328707731712 GraphCoverageDescriptions.GraphCoverageBatch015.candidate01501 14

certified_graph_case record006 16 25367741005824 GraphCoverageDescriptions.GraphCoverageBatch015.candidate01502 14

certified_graph_case record007 16 25398960750848 GraphCoverageDescriptions.GraphCoverageBatch015.candidate01503 14

certified_graph_case record008 16 25400038195200 GraphCoverageDescriptions.GraphCoverageBatch015.candidate01504 14

certified_graph_case record009 16 25414600818688 GraphCoverageDescriptions.GraphCoverageBatch015.candidate01505 14

certified_graph_case record010 16 25415641006080 GraphCoverageDescriptions.GraphCoverageBatch015.candidate01506 14

certified_graph_case record011 16 25633592738048 GraphCoverageDescriptions.GraphCoverageBatch015.candidate01507 14

certified_graph_case record012 16 25639009157376 GraphCoverageDescriptions.GraphCoverageBatch015.candidate01508 14

certified_graph_case record013 16 25671221149952 GraphCoverageDescriptions.GraphCoverageBatch015.candidate01509 14

certified_graph_case record014 16 25841922769152 GraphCoverageDescriptions.GraphCoverageBatch015.candidate01510 14

certified_graph_case record015 16 25877354414336 GraphCoverageDescriptions.GraphCoverageBatch015.candidate01511 14

certified_graph_case record016 16 25878423732480 GraphCoverageDescriptions.GraphCoverageBatch015.candidate01512 14

certified_graph_case record017 16 25878923346176 GraphCoverageDescriptions.GraphCoverageBatch015.candidate01513 14

certified_graph_case record018 16 25895603601408 GraphCoverageDescriptions.GraphCoverageBatch015.candidate01514 14

theorem record019_parameters : Parameters record019 (rowOfCode 16) 25915333607424 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record019_coverage : Coverage record019 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25915333607424 :=
  GraphCoverageDescriptions.coverage_of_checked record019 GraphCoverageDescriptions.GraphCoverageBatch015.candidate01515 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25915333607424
    (by rfl) record019_cells_exact
    (GraphCoverageDescriptions.small_allowed record019 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch015.candidate01515_checked

theorem record019_result : Result (16, 25915333607424) :=
  of_direct_small 16 25915333607424 (by decide) ⟨record019, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00025.record019.direct_core, record019_parameters, record019_coverage⟩
#print axioms record019_result

theorem record020_parameters : Parameters record020 (rowOfCode 16) 25915341930496 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record020_coverage : Coverage record020 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25915341930496 :=
  GraphCoverageDescriptions.coverage_of_checked record020 GraphCoverageDescriptions.GraphCoverageBatch015.candidate01516 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25915341930496
    (by rfl) record020_cells_exact
    (GraphCoverageDescriptions.small_allowed record020 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch015.candidate01516_checked

theorem record020_result : Result (16, 25915341930496) :=
  of_direct_small 16 25915341930496 (by decide) ⟨record020, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00025.record020.direct_core, record020_parameters, record020_coverage⟩
#print axioms record020_result

certified_graph_case record021 16 25925698224384 GraphCoverageDescriptions.GraphCoverageBatch015.candidate01517 14

theorem record022_parameters : Parameters record022 (rowOfCode 16) 25927815856128 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record022_coverage : Coverage record022 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25927815856128 :=
  GraphCoverageDescriptions.coverage_of_checked record022 GraphCoverageDescriptions.GraphCoverageBatch015.candidate01518 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25927815856128
    (by rfl) record022_cells_exact
    (GraphCoverageDescriptions.small_allowed record022 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch015.candidate01518_checked

theorem record022_result : Result (16, 25927815856128) :=
  of_direct_small 16 25927815856128 (by decide) ⟨record022, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00025.record022.direct_core, record022_parameters, record022_coverage⟩
#print axioms record022_result

theorem record023_parameters : Parameters record023 (rowOfCode 16) 25931175952384 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record023_coverage : Coverage record023 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25931175952384 :=
  GraphCoverageDescriptions.coverage_of_checked record023 GraphCoverageDescriptions.GraphCoverageBatch015.candidate01519 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25931175952384
    (by rfl) record023_cells_exact
    (GraphCoverageDescriptions.small_allowed record023 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch015.candidate01519_checked

theorem record023_result : Result (16, 25931175952384) :=
  of_direct_small 16 25931175952384 (by decide) ⟨record023, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00025.record023.direct_core, record023_parameters, record023_coverage⟩
#print axioms record023_result

certified_graph_case record024 16 25942831464704 GraphCoverageDescriptions.GraphCoverageBatch015.candidate01520 14

certified_graph_case record025 16 25943347593472 GraphCoverageDescriptions.GraphCoverageBatch015.candidate01521 14

certified_graph_case record026 16 25946451640576 GraphCoverageDescriptions.GraphCoverageBatch015.candidate01522 14

certified_graph_case record027 16 25946468155648 GraphCoverageDescriptions.GraphCoverageBatch015.candidate01523 14

certified_graph_case record028 16 25963094638848 GraphCoverageDescriptions.GraphCoverageBatch015.candidate01524 14

certified_graph_case record029 16 25963131895808 GraphCoverageDescriptions.GraphCoverageBatch015.candidate01525 14

certified_graph_case record030 16 25963140218880 GraphCoverageDescriptions.GraphCoverageBatch015.candidate01526 14

certified_graph_case record031 16 25963363106816 GraphCoverageDescriptions.GraphCoverageBatch015.candidate01527 14

certified_graph_case record032 16 25963371429888 GraphCoverageDescriptions.GraphCoverageBatch015.candidate01528 14

certified_graph_case record033 16 25963387944960 GraphCoverageDescriptions.GraphCoverageBatch015.candidate01529 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025

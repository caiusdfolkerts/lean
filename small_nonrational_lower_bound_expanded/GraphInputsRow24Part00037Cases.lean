module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00037Checked
public import GraphInputsRow24Part00037Metadata
public import GraphInputsRow24Part00037Frames
public import GraphInputsRow24Part00037Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch077
public import GraphInputsRow24Part00037Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00037
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 24) 17198328381440 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 17198328381440 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07747 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 17198328381440
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch077.candidate07747_checked

theorem record000_result : Result (24, 17198328381440) :=
  of_direct_small 24 17198328381440 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00037.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 24 17198336704512 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07748 14

certified_graph_case record002 24 17198468825088 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07749 14

certified_graph_case record003 24 17198525448960 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07750 14

certified_graph_case record004 24 17199232221440 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07751 14

certified_graph_case record005 24 17202149327376 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07752 14

certified_graph_case record006 24 17215441142016 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07753 14

certified_graph_case record007 24 17219874521088 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07754 14

theorem record008_parameters : Parameters record008 (rowOfCode 24) 17220411326464 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 17220411326464 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07755 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 17220411326464
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch077.candidate07755_checked

theorem record008_result : Result (24, 17220411326464) :=
  of_direct_small 24 17220411326464 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00037.record008.direct_core, record008_parameters, record008_coverage⟩

theorem record009_parameters : Parameters record009 (rowOfCode 24) 17224572076032 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 17224572076032 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07756 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 17224572076032
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.small_allowed record009 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch077.candidate07756_checked

theorem record009_result : Result (24, 17224572076032) :=
  of_direct_small 24 17224572076032 (by decide) ⟨record009, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00037.record009.direct_core, record009_parameters, record009_coverage⟩

certified_graph_case record010 24 17227114021120 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07757 14

certified_graph_case record011 24 17227155832832 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07758 14

certified_graph_case record012 24 17228732825600 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07759 14

theorem record013_parameters : Parameters record013 (rowOfCode 24) 17232621010944 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record013_coverage : Coverage record013 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 17232621010944 :=
  GraphCoverageDescriptions.coverage_of_checked record013 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07760 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 17232621010944
    (by rfl) record013_cells_exact
    (GraphCoverageDescriptions.small_allowed record013 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch077.candidate07760_checked

theorem record013_result : Result (24, 17232621010944) :=
  of_direct_small 24 17232621010944 (by decide) ⟨record013, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00037.record013.direct_core, record013_parameters, record013_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00037

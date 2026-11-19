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

certified_graph_case record000 24 17198328381440 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07747 14

certified_graph_case record001 24 17198336704512 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07748 14

certified_graph_case record002 24 17198468825088 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07749 14

certified_graph_case record003 24 17198525448960 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07750 14

certified_graph_case record004 24 17199232221440 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07751 14

certified_graph_case record005 24 17202149327376 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07752 14

certified_graph_case record006 24 17215441142016 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07753 14

certified_graph_case record007 24 17219874521088 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07754 14

certified_graph_case record008 24 17220411326464 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07755 14

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
#print axioms record009_result

certified_graph_case record010 24 17227114021120 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07757 14

certified_graph_case record011 24 17227155832832 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07758 14

certified_graph_case record012 24 17228732825600 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07759 14

certified_graph_case record013 24 17232621010944 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07760 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00037

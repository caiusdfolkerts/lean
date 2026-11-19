module
prelude
public meta import GraphCases
public import GraphInputsRow26Part00027Checked
public import GraphInputsRow26Part00027Metadata
public import GraphInputsRow26Part00027Frames
public import GraphInputsRow26Part00027Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch077
public import GraphCoverageBatch128
public import GraphInputsRow26Part00027Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 26 17199232221440 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07751 14

certified_graph_case record001 26 17202149327376 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07752 14

certified_graph_case record002 26 17215441142016 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07753 14

certified_graph_case record003 26 17219874521088 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07754 14

certified_graph_case record004 26 17220411326464 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07755 14

certified_graph_case record005 26 17224572076032 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07756 14

certified_graph_case record006 26 17227155832832 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07758 14

certified_graph_case record007 26 17228732825600 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07759 14

certified_graph_case record008 26 17232621010944 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07760 14

certified_graph_case record009 26 17232893575168 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07761 14

certified_graph_case record010 26 17235741573120 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07763 14

certified_graph_case record011 26 17236509589504 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07765 14

theorem record012_parameters : Parameters record012 (rowOfCode 26) 17237054324736 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record012_coverage : Coverage record012 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 17237054324736 :=
  GraphCoverageDescriptions.coverage_of_checked record012 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07766 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 17237054324736
    (by rfl) record012_cells_exact
    (GraphCoverageDescriptions.small_allowed record012 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch077.candidate07766_checked

theorem record012_result : Result (26, 17237054324736) :=
  of_direct_small 26 17237054324736 (by decide) ⟨record012, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00027.record012.direct_core, record012_parameters, record012_coverage⟩

theorem record013_parameters : Parameters record013 (rowOfCode 26) 17244335636480 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record013_coverage : Coverage record013 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 17244335636480 :=
  GraphCoverageDescriptions.coverage_of_checked record013 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07767 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 17244335636480
    (by rfl) record013_cells_exact
    (GraphCoverageDescriptions.small_allowed record013 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch077.candidate07767_checked

theorem record013_result : Result (26, 17244335636480) :=
  of_direct_small 26 17244335636480 (by decide) ⟨record013, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00027.record013.direct_core, record013_parameters, record013_coverage⟩

certified_graph_case record014 26 17292100370432 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07771 14

certified_graph_case record015 26 17300149305344 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07772 14

certified_graph_case record016 26 17300933836800 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07773 14

certified_graph_case record017 26 17317329307664 GraphCoverageDescriptions.GraphCoverageBatch128.candidate12801 14

certified_graph_case record018 26 17328448798720 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07776 14

certified_graph_case record019 26 17361742594048 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07777 14

certified_graph_case record020 26 17429270888448 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07778 14

certified_graph_case record021 26 17455890071808 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07779 14

certified_graph_case record022 26 17458106793984 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07780 14

certified_graph_case record023 26 17458379358208 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07781 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027

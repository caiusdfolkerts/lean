module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00013Checked
public import GraphInputsRow29Part00013Metadata
public import GraphInputsRow29Part00013Frames
public import GraphInputsRow29Part00013Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch106
public import GraphCoverageBatch143
public import GraphInputsRow29Part00013Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00013
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 3240963932160 GraphCoverageDescriptions.GraphCoverageBatch143.candidate14361 14

certified_graph_case record001 29 3241228173312 GraphCoverageDescriptions.GraphCoverageBatch143.candidate14362 14

certified_graph_case record002 29 3241236496384 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10677 14

certified_graph_case record003 29 3243308548096 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10678 14

certified_graph_case record004 29 3243316871168 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10679 14

certified_graph_case record005 29 3249281204480 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10680 14

certified_graph_case record006 29 3249818075136 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10681 14

certified_graph_case record007 29 3249950195712 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10682 14

certified_graph_case record008 29 3255654449408 GraphCoverageDescriptions.GraphCoverageBatch143.candidate14363 14

theorem record009_parameters : Parameters record009 (rowOfCode 29) 3338676502784 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 3338676502784 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10683 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 3338676502784
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.small_allowed record009 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch106.candidate10683_checked

theorem record009_result : Result (29, 3338676502784) :=
  of_direct_small 29 3338676502784 (by decide) ⟨record009, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00013.record009.direct_core, record009_parameters, record009_coverage⟩
#print axioms record009_result

certified_graph_case record010 29 3372969132288 GraphCoverageDescriptions.GraphCoverageBatch143.candidate14364 14

certified_graph_case record011 29 3377129881856 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10684 14

certified_graph_case record012 29 3415174349056 GraphCoverageDescriptions.GraphCoverageBatch143.candidate14365 14

certified_graph_case record013 29 3423764250880 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10685 14

certified_graph_case record014 29 3423772639232 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10686 14

certified_graph_case record015 29 3492490018816 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10687 14

certified_graph_case record016 29 3524702273536 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10688 14

certified_graph_case record017 29 3527447478272 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10689 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00013

module
prelude
public meta import GraphCases
public import GraphInputsRow26Part00081Checked
public import GraphInputsRow26Part00081Metadata
public import GraphInputsRow26Part00081Frames
public import GraphInputsRow26Part00081Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch103
public import GraphCoverageBatch104
public import GraphCoverageBatch130
public import GraphInputsRow26Part00081Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00081
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 26 34088358645824 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10398 14

certified_graph_case record001 26 34088394162177 GraphCoverageDescriptions.GraphCoverageBatch130.candidate13081 14

certified_graph_case record002 26 34090398023936 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10399 14

certified_graph_case record003 26 34093561546768 GraphCoverageDescriptions.GraphCoverageBatch130.candidate13082 14

certified_graph_case record004 26 34094007193616 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10401 14

certified_graph_case record005 26 34094023968784 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10402 14

theorem record006_parameters : Parameters record006 (rowOfCode 26) 34095097708545 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34095097708545 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10403 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 34095097708545
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch104.candidate10403_checked

theorem record006_result : Result (26, 34095097708545) :=
  of_direct_small 26 34095097708545 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00081.record006.direct_core, record006_parameters, record006_coverage⟩
#print axioms record006_result

certified_graph_case record007 26 34119375655168 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10404 14

certified_graph_case record008 26 34119514067008 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10405 14

certified_graph_case record009 26 34123792123920 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10407 14

certified_graph_case record010 26 34123809292289 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10408 14

certified_graph_case record011 26 34124794494976 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10409 14

certified_graph_case record012 26 34124865863681 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10410 14

certified_graph_case record013 26 34127952873488 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10411 14

certified_graph_case record014 26 34155878973696 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10412 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00081

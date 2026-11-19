module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00229Checked
public import GraphInputsRow29Part00229Metadata
public import GraphInputsRow29Part00229Frames
public import GraphInputsRow29Part00229Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch121
public import GraphCoverageBatch154
public import GraphInputsRow29Part00229Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00229
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 30865254129696 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12106 14

certified_graph_case record001 29 30865313792256 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15469 14

certified_graph_case record002 29 30865322147841 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12107 14

certified_graph_case record003 29 30865325301760 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12108 14

certified_graph_case record004 29 30865515094272 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12109 14

certified_graph_case record005 29 30866327867424 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12110 14

certified_graph_case record006 29 30866362335233 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12111 14

certified_graph_case record007 29 30866588311808 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12112 14

certified_graph_case record008 29 30873639518208 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12113 14

theorem record009_parameters : Parameters record009 (rowOfCode 29) 30881620697120 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 30881620697120 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12114 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 30881620697120
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.small_allowed record009 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch121.candidate12114_checked

theorem record009_result : Result (29, 30881620697120) :=
  of_direct_small 29 30881620697120 (by decide) ⟨record009, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00229.record009.direct_core, record009_parameters, record009_coverage⟩
#print axioms record009_result

certified_graph_case record010 29 30896119939328 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15470 14

certified_graph_case record011 29 30896656809984 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12115 14

certified_graph_case record012 29 30896665133056 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12116 14

certified_graph_case record013 29 30898281054464 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15471 14

certified_graph_case record014 29 30898289442816 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15472 14

certified_graph_case record015 29 30898549457152 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15473 14

certified_graph_case record016 29 30898553683968 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15474 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00229

module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00160Checked
public import GraphInputsRow24Part00160Metadata
public import GraphInputsRow24Part00160Frames
public import GraphInputsRow24Part00160Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch103
public import GraphInputsRow24Part00160Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00160
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 32933809358880 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10328 14

certified_graph_case record001 24 32935956709892 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10329 14

certified_graph_case record002 24 32988877308160 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10330 14

certified_graph_case record003 24 32991025832192 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10331 14

certified_graph_case record004 24 33022146003200 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10332 14

certified_graph_case record005 24 33023338807296 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10333 14

certified_graph_case record006 24 33025419182080 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10334 14

certified_graph_case record007 24 33032996659456 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10335 14

theorem record008_parameters : Parameters record008 (rowOfCode 24) 33058653217024 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 33058653217024 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10336 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 33058653217024
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch103.candidate10336_checked

theorem record008_result : Result (24, 33058653217024) :=
  of_direct_small 24 33058653217024 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00160.record008.direct_core, record008_parameters, record008_coverage⟩
#print axioms record008_result

certified_graph_case record009 24 33059777871872 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10337 14

certified_graph_case record010 24 33063938621440 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10338 14

certified_graph_case record011 24 33064135696640 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10339 14

certified_graph_case record012 24 33065208914176 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10340 14

certified_graph_case record013 24 33098495492096 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10341 14

certified_graph_case record014 24 33102730625024 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10342 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00160

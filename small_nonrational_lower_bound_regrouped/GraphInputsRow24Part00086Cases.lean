module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00086Checked
public import GraphInputsRow24Part00086Metadata
public import GraphInputsRow24Part00086Frames
public import GraphInputsRow24Part00086Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch090
public import GraphInputsRow24Part00086Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00086
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 24617176547328 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09040 14

certified_graph_case record001 24 24620162891840 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09041 14

certified_graph_case record002 24 24621303210048 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09042 14

certified_graph_case record003 24 24628484390976 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09043 14

theorem record004_parameters : Parameters record004 (rowOfCode 24) 24628618608640 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24628618608640 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09044 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24628618608640
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch090.candidate09044_checked

theorem record004_result : Result (24, 24628618608640) :=
  of_direct_small 24 24628618608640 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00086.record004.direct_core, record004_parameters, record004_coverage⟩
#print axioms record004_result

certified_graph_case record005 24 24628620689408 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09045 14

certified_graph_case record006 24 24629524578368 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09046 14

certified_graph_case record007 24 24629592735744 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09047 14

certified_graph_case record008 24 24629658796032 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09048 14

certified_graph_case record009 24 24629660876800 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09049 14

certified_graph_case record010 24 24638233018624 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09050 14

certified_graph_case record011 24 24638237245440 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09051 14

certified_graph_case record012 24 24638243487744 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09052 14

certified_graph_case record013 24 24638367219968 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09053 14

certified_graph_case record014 24 24638375608320 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09054 14

certified_graph_case record015 24 24638482825472 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09055 14

certified_graph_case record016 24 24638493034496 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09056 14

certified_graph_case record017 24 24638885478464 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09057 14

certified_graph_case record018 24 24640383680512 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09058 14

certified_graph_case record019 24 24640428998912 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09059 14

certified_graph_case record020 24 24640441288704 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09060 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00086

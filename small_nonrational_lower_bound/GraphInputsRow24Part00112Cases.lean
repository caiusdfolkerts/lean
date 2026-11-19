module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00112Checked
public import GraphInputsRow24Part00112Metadata
public import GraphInputsRow24Part00112Frames
public import GraphInputsRow24Part00112Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch095
public import GraphInputsRow24Part00112Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00112
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 27687105085440 GraphCoverageDescriptions.GraphCoverageBatch095.candidate09576 14

certified_graph_case record001 24 27689688776960 GraphCoverageDescriptions.GraphCoverageBatch095.candidate09577 14

theorem record002_parameters : Parameters record002 (rowOfCode 24) 27689756983296 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 27689756983296 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch095.candidate09578 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 27689756983296
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch095.candidate09578_checked

theorem record002_result : Result (24, 27689756983296) :=
  of_direct_small 24 27689756983296 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00112.record002.direct_core, record002_parameters, record002_coverage⟩
#print axioms record002_result

theorem record003_parameters : Parameters record003 (rowOfCode 24) 27689765306368 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 27689765306368 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch095.candidate09579 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 27689765306368
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch095.candidate09579_checked

theorem record003_result : Result (24, 27689765306368) :=
  of_direct_small 24 27689765306368 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00112.record003.direct_core, record003_parameters, record003_coverage⟩
#print axioms record003_result

certified_graph_case record004 24 27690225647616 GraphCoverageDescriptions.GraphCoverageBatch095.candidate09580 14

certified_graph_case record005 24 27697508057344 GraphCoverageDescriptions.GraphCoverageBatch095.candidate09581 14

certified_graph_case record006 24 27697786929152 GraphCoverageDescriptions.GraphCoverageBatch095.candidate09582 14

certified_graph_case record007 24 27704226234368 GraphCoverageDescriptions.GraphCoverageBatch095.candidate09583 14

certified_graph_case record008 24 27712547733504 GraphCoverageDescriptions.GraphCoverageBatch095.candidate09584 14

certified_graph_case record009 24 27721969238016 GraphCoverageDescriptions.GraphCoverageBatch095.candidate09585 14

certified_graph_case record010 24 27721977561088 GraphCoverageDescriptions.GraphCoverageBatch095.candidate09586 14

certified_graph_case record011 24 27730743722240 GraphCoverageDescriptions.GraphCoverageBatch095.candidate09587 14

certified_graph_case record012 24 27730752110592 GraphCoverageDescriptions.GraphCoverageBatch095.candidate09588 14

certified_graph_case record013 24 27730859327744 GraphCoverageDescriptions.GraphCoverageBatch095.candidate09589 14

certified_graph_case record014 24 27731012124928 GraphCoverageDescriptions.GraphCoverageBatch095.candidate09590 14

certified_graph_case record015 24 27731016351744 GraphCoverageDescriptions.GraphCoverageBatch095.candidate09591 14

certified_graph_case record016 24 27731022594048 GraphCoverageDescriptions.GraphCoverageBatch095.candidate09592 14

certified_graph_case record017 24 27731127730432 GraphCoverageDescriptions.GraphCoverageBatch095.candidate09593 14

certified_graph_case record018 24 27731140020224 GraphCoverageDescriptions.GraphCoverageBatch095.candidate09594 14

certified_graph_case record019 24 27731261931776 GraphCoverageDescriptions.GraphCoverageBatch095.candidate09595 14

certified_graph_case record020 24 27735426662400 GraphCoverageDescriptions.GraphCoverageBatch095.candidate09596 14

certified_graph_case record021 24 27737461899264 GraphCoverageDescriptions.GraphCoverageBatch095.candidate09597 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00112

module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00062Checked
public import GraphInputsRow24Part00062Metadata
public import GraphInputsRow24Part00062Frames
public import GraphInputsRow24Part00062Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch085
public import GraphInputsRow24Part00062Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00062
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 22851929800960 GraphCoverageDescriptions.GraphCoverageBatch085.candidate08519 14

certified_graph_case record001 24 22851954411648 GraphCoverageDescriptions.GraphCoverageBatch085.candidate08520 14

certified_graph_case record002 24 22853265145856 GraphCoverageDescriptions.GraphCoverageBatch085.candidate08521 14

certified_graph_case record003 24 22859227398400 GraphCoverageDescriptions.GraphCoverageBatch085.candidate08522 14

certified_graph_case record004 24 22859495801088 GraphCoverageDescriptions.GraphCoverageBatch085.candidate08523 14

certified_graph_case record005 24 22859506270208 GraphCoverageDescriptions.GraphCoverageBatch085.candidate08524 14

certified_graph_case record006 24 22862783086848 GraphCoverageDescriptions.GraphCoverageBatch085.candidate08525 14

certified_graph_case record007 24 22866517035136 GraphCoverageDescriptions.GraphCoverageBatch085.candidate08526 14

certified_graph_case record008 24 22867817300224 GraphCoverageDescriptions.GraphCoverageBatch085.candidate08527 14

certified_graph_case record009 24 22867827769344 GraphCoverageDescriptions.GraphCoverageBatch085.candidate08528 14

certified_graph_case record010 24 22869761491200 GraphCoverageDescriptions.GraphCoverageBatch085.candidate08529 14

theorem record011_parameters : Parameters record011 (rowOfCode 24) 22869769879552 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record011_coverage : Coverage record011 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 22869769879552 :=
  GraphCoverageDescriptions.coverage_of_checked record011 GraphCoverageDescriptions.GraphCoverageBatch085.candidate08530 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 22869769879552
    (by rfl) record011_cells_exact
    (GraphCoverageDescriptions.small_allowed record011 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch085.candidate08530_checked

theorem record011_result : Result (24, 22869769879552) :=
  of_direct_small 24 22869769879552 (by decide) ⟨record011, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00062.record011.direct_core, record011_parameters, record011_coverage⟩
#print axioms record011_result

certified_graph_case record012 24 22870298198656 GraphCoverageDescriptions.GraphCoverageBatch085.candidate08531 14

certified_graph_case record013 24 22876407267328 GraphCoverageDescriptions.GraphCoverageBatch085.candidate08532 14

certified_graph_case record014 24 22876944072704 GraphCoverageDescriptions.GraphCoverageBatch085.candidate08533 14

certified_graph_case record015 24 22924660637952 GraphCoverageDescriptions.GraphCoverageBatch085.candidate08534 14

certified_graph_case record016 24 22925197508608 GraphCoverageDescriptions.GraphCoverageBatch085.candidate08535 14

certified_graph_case record017 24 22925205831680 GraphCoverageDescriptions.GraphCoverageBatch085.candidate08536 14

certified_graph_case record018 24 22928821387520 GraphCoverageDescriptions.GraphCoverageBatch085.candidate08537 14

certified_graph_case record019 24 22929094017024 GraphCoverageDescriptions.GraphCoverageBatch085.candidate08538 14

certified_graph_case record020 24 22929358258176 GraphCoverageDescriptions.GraphCoverageBatch085.candidate08539 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00062

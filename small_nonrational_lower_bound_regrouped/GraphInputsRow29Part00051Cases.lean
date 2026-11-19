module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00051Checked
public import GraphInputsRow29Part00051Metadata
public import GraphInputsRow29Part00051Frames
public import GraphInputsRow29Part00051Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch110
public import GraphCoverageBatch145
public import GraphInputsRow29Part00051Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00051
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 9803401330944 GraphCoverageDescriptions.GraphCoverageBatch145.candidate14537 14

certified_graph_case record001 29 9811991232768 GraphCoverageDescriptions.GraphCoverageBatch145.candidate14538 14

certified_graph_case record002 29 9812660224000 GraphCoverageDescriptions.GraphCoverageBatch145.candidate14539 14

certified_graph_case record003 29 9820581199872 GraphCoverageDescriptions.GraphCoverageBatch145.candidate14540 14

theorem record004_parameters : Parameters record004 (rowOfCode 29) 9820853764096 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 9820853764096 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11054 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 9820853764096
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch110.candidate11054_checked

theorem record004_result : Result (29, 9820853764096) :=
  of_direct_small 29 9820853764096 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00051.record004.direct_core, record004_parameters, record004_coverage⟩
#print axioms record004_result

certified_graph_case record005 29 9821118005248 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11055 14

certified_graph_case record006 29 9933594624256 GraphCoverageDescriptions.GraphCoverageBatch145.candidate14541 14

certified_graph_case record007 29 9935679225856 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11056 14

certified_graph_case record008 29 9936822079744 GraphCoverageDescriptions.GraphCoverageBatch145.candidate14542 14

certified_graph_case record009 29 9939839910144 GraphCoverageDescriptions.GraphCoverageBatch145.candidate14543 14

certified_graph_case record010 29 9941114949888 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11057 14

certified_graph_case record011 29 9943261384960 GraphCoverageDescriptions.GraphCoverageBatch145.candidate14544 14

certified_graph_case record012 29 9970309431552 GraphCoverageDescriptions.GraphCoverageBatch145.candidate14545 14

certified_graph_case record013 29 9970309496832 GraphCoverageDescriptions.GraphCoverageBatch145.candidate14546 14

certified_graph_case record014 29 9970510733568 GraphCoverageDescriptions.GraphCoverageBatch145.candidate14547 14

certified_graph_case record015 29 9974602366976 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11058 14

certified_graph_case record016 29 9974671483136 GraphCoverageDescriptions.GraphCoverageBatch145.candidate14548 14

certified_graph_case record017 29 10010104954881 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11059 14

certified_graph_case record018 29 10055202115616 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11060 14

certified_graph_case record019 29 10072977637632 GraphCoverageDescriptions.GraphCoverageBatch145.candidate14549 14

certified_graph_case record020 29 10090165829632 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11061 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00051

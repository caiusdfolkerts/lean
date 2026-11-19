module
prelude
public meta import GraphCases
public import GraphInputsRow26Part00008Checked
public import GraphInputsRow26Part00008Metadata
public import GraphInputsRow26Part00008Frames
public import GraphInputsRow26Part00008Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch065
public import GraphCoverageBatch066
public import GraphCoverageBatch125
public import GraphInputsRow26Part00008Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00008
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 26 5892764565512 GraphCoverageDescriptions.GraphCoverageBatch125.candidate12551 14

certified_graph_case record001 26 5895660519424 GraphCoverageDescriptions.GraphCoverageBatch065.candidate06581 14

certified_graph_case record002 26 5899150164996 GraphCoverageDescriptions.GraphCoverageBatch065.candidate06583 14

certified_graph_case record003 26 5899414405636 GraphCoverageDescriptions.GraphCoverageBatch065.candidate06584 14

certified_graph_case record004 26 5899414536193 GraphCoverageDescriptions.GraphCoverageBatch065.candidate06585 14

certified_graph_case record005 26 5899687035904 GraphCoverageDescriptions.GraphCoverageBatch065.candidate06586 14

certified_graph_case record006 26 5904116219904 GraphCoverageDescriptions.GraphCoverageBatch065.candidate06589 14

certified_graph_case record007 26 5904380461056 GraphCoverageDescriptions.GraphCoverageBatch065.candidate06591 14

certified_graph_case record008 26 5972833599488 GraphCoverageDescriptions.GraphCoverageBatch065.candidate06595 14

certified_graph_case record009 26 5974905651200 GraphCoverageDescriptions.GraphCoverageBatch065.candidate06598 14

certified_graph_case record010 26 5974913974272 GraphCoverageDescriptions.GraphCoverageBatch065.candidate06599 14

certified_graph_case record011 26 5998538407936 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06600 14

certified_graph_case record012 26 6340532011264 GraphCoverageDescriptions.GraphCoverageBatch125.candidate12552 14

certified_graph_case record013 26 6343310180352 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06601 14

certified_graph_case record014 26 6379104503040 GraphCoverageDescriptions.GraphCoverageBatch125.candidate12553 14

certified_graph_case record015 26 6379104568320 GraphCoverageDescriptions.GraphCoverageBatch125.candidate12554 14

theorem record016_parameters : Parameters record016 (rowOfCode 26) 6379112760324 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record016_coverage : Coverage record016 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 6379112760324 :=
  GraphCoverageDescriptions.coverage_of_checked record016 GraphCoverageDescriptions.GraphCoverageBatch125.candidate12555 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 6379112760324
    (by rfl) record016_cells_exact
    (GraphCoverageDescriptions.small_allowed record016 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch125.candidate12555_checked

theorem record016_result : Result (26, 6379112760324) :=
  of_direct_small 26 6379112760324 (by decide) ⟨record016, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00008.record016.direct_core, record016_parameters, record016_coverage⟩

certified_graph_case record017 26 6379377000964 GraphCoverageDescriptions.GraphCoverageBatch125.candidate12556 14

certified_graph_case record018 26 6379377131521 GraphCoverageDescriptions.GraphCoverageBatch125.candidate12557 14

certified_graph_case record019 26 6379649631232 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06602 14

certified_graph_case record020 26 6379918065664 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06603 14

certified_graph_case record021 26 6443268835328 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06605 14

certified_graph_case record022 26 6447563800576 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06606 14

certified_graph_case record023 26 6451871350784 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06607 14

certified_graph_case record024 26 6456149540864 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06608 14

certified_graph_case record025 26 6487088824320 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06609 14

certified_graph_case record026 26 6511854094336 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06610 14

certified_graph_case record027 26 6524592390144 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06611 14

certified_graph_case record028 26 6524600713216 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06612 14

certified_graph_case record029 26 6548361314304 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06613 14

certified_graph_case record030 26 6559027429376 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06614 14

certified_graph_case record031 26 6633730703744 GraphCoverageDescriptions.GraphCoverageBatch125.candidate12558 14

certified_graph_case record032 26 6633732784512 GraphCoverageDescriptions.GraphCoverageBatch125.candidate12559 14

certified_graph_case record033 26 6701436731400 GraphCoverageDescriptions.GraphCoverageBatch125.candidate12560 14

certified_graph_case record034 26 6701511180544 GraphCoverageDescriptions.GraphCoverageBatch125.candidate12561 14

certified_graph_case record035 26 6701513261312 GraphCoverageDescriptions.GraphCoverageBatch125.candidate12562 14

theorem record036_parameters : Parameters record036 (rowOfCode 26) 6701568851976 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record036_coverage : Coverage record036 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 6701568851976 :=
  GraphCoverageDescriptions.coverage_of_checked record036 GraphCoverageDescriptions.GraphCoverageBatch125.candidate12563 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 6701568851976
    (by rfl) record036_cells_exact
    (GraphCoverageDescriptions.small_allowed record036 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch125.candidate12563_checked

theorem record036_result : Result (26, 6701568851976) :=
  of_direct_small 26 6701568851976 (by decide) ⟨record036, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00008.record036.direct_core, record036_parameters, record036_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00008

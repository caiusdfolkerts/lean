module
prelude
public meta import GraphCases
public import GraphInputsRow30Part00006Checked
public import GraphInputsRow30Part00006Metadata
public import GraphInputsRow30Part00006Frames
public import GraphInputsRow30Part00006Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch107
public import GraphCoverageBatch155
public import GraphInputsRow30Part00006Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00006
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 30 4451270181120 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15542 14

theorem record001_parameters : Parameters record001 (rowOfCode 30) 4485233606688 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 4485233606688 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch107.candidate10757 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 4485233606688
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch107.candidate10757_checked

theorem record001_result : Result (30, 4485233606688) :=
  of_direct_small 30 4485233606688 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00006.record001.direct_core, record001_parameters, record001_coverage⟩

certified_graph_case record002 30 4485364629760 GraphCoverageDescriptions.GraphCoverageBatch107.candidate10758 14

certified_graph_case record003 30 4485365727264 GraphCoverageDescriptions.GraphCoverageBatch107.candidate10759 14

theorem record004_parameters : Parameters record004 (rowOfCode 30) 4485629968416 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 4485629968416 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch107.candidate10760 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 4485629968416
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch107.candidate10760_checked

theorem record004_result : Result (30, 4485629968416) :=
  of_direct_small 30 4485629968416 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00006.record004.direct_core, record004_parameters, record004_coverage⟩

certified_graph_case record005 30 4521136848896 GraphCoverageDescriptions.GraphCoverageBatch107.candidate10761 14

certified_graph_case record006 30 4553943646464 GraphCoverageDescriptions.GraphCoverageBatch107.candidate10762 14

certified_graph_case record007 30 4658498142464 GraphCoverageDescriptions.GraphCoverageBatch107.candidate10763 14

certified_graph_case record008 30 4691384647936 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15543 14

theorem record009_parameters : Parameters record009 (rowOfCode 30) 4691385745440 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 4691385745440 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15544 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 4691385745440
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.small_allowed record009 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch155.candidate15544_checked

theorem record009_result : Result (30, 4691385745440) :=
  of_direct_small 30 4691385745440 (by decide) ⟨record009, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00006.record009.direct_core, record009_parameters, record009_coverage⟩

certified_graph_case record010 30 4691788349472 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15545 14

certified_graph_case record011 30 4953754140704 GraphCoverageDescriptions.GraphCoverageBatch107.candidate10764 14

certified_graph_case record012 30 4958047010848 GraphCoverageDescriptions.GraphCoverageBatch107.candidate10765 14

certified_graph_case record013 30 4966632751136 GraphCoverageDescriptions.GraphCoverageBatch107.candidate10766 14

certified_graph_case record014 30 5025405935872 GraphCoverageDescriptions.GraphCoverageBatch107.candidate10767 14

certified_graph_case record015 30 5025674395680 GraphCoverageDescriptions.GraphCoverageBatch107.candidate10768 14

certified_graph_case record016 30 5089830445312 GraphCoverageDescriptions.GraphCoverageBatch107.candidate10769 14

certified_graph_case record017 30 5102983757856 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15546 14

certified_graph_case record018 30 5104109453312 GraphCoverageDescriptions.GraphCoverageBatch107.candidate10770 14

certified_graph_case record019 30 5123505979392 GraphCoverageDescriptions.GraphCoverageBatch107.candidate10771 14

certified_graph_case record020 30 5138460737792 GraphCoverageDescriptions.GraphCoverageBatch107.candidate10772 14

certified_graph_case record021 30 5140677459968 GraphCoverageDescriptions.GraphCoverageBatch107.candidate10773 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00006

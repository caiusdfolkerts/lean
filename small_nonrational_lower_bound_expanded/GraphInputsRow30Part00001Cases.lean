module
prelude
public meta import GraphCases
public import GraphInputsRow30Part00001Checked
public import GraphInputsRow30Part00001Metadata
public import GraphInputsRow30Part00001Frames
public import GraphInputsRow30Part00001Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch105
public import GraphInputsRow30Part00001Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00001
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 30 801695137792 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10510 14

certified_graph_case record001 30 805583257856 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10511 14

certified_graph_case record002 30 806120128512 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10512 14

theorem record003_parameters : Parameters record003 (rowOfCode 30) 810408771840 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 810408771840 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10513 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 810408771840
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch105.candidate10513_checked

theorem record003_result : Result (30, 810408771840) :=
  of_direct_small 30 810408771840 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00001.record003.direct_core, record003_parameters, record003_coverage⟩

certified_graph_case record004 30 814168998144 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10514 14

certified_graph_case record005 30 814705868800 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10515 14

certified_graph_case record006 30 814714191872 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10516 14

certified_graph_case record007 30 818329747712 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10517 14

certified_graph_case record008 30 818602377216 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10518 14

certified_graph_case record009 30 818866618368 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10519 14

certified_graph_case record010 30 818874941440 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10520 14

certified_graph_case record011 30 819139182592 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10521 14

certified_graph_case record012 30 872562130944 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10522 14

certified_graph_case record013 30 881286201472 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10523 14

certified_graph_case record014 30 915645931648 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10524 14

certified_graph_case record015 30 938857267456 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10525 14

certified_graph_case record016 30 938865655808 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10526 14

certified_graph_case record017 30 1003281776896 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10527 14

certified_graph_case record018 30 1003290165248 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10528 14

certified_graph_case record019 30 1003682300160 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10529 14

theorem record020_parameters : Parameters record020 (rowOfCode 30) 1007583035392 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record020_coverage : Coverage record020 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 1007583035392 :=
  GraphCoverageDescriptions.coverage_of_checked record020 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10530 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 1007583035392
    (by rfl) record020_cells_exact
    (GraphCoverageDescriptions.small_allowed record020 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch105.candidate10530_checked

theorem record020_result : Result (30, 1007583035392) :=
  of_direct_small 30 1007583035392 (by decide) ⟨record020, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00001.record020.direct_core, record020_parameters, record020_coverage⟩

certified_graph_case record021 30 1007843049728 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10531 14

certified_graph_case record022 30 1016168775680 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10532 14

certified_graph_case record023 30 1026566422784 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10533 14

certified_graph_case record024 30 1026702770176 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10534 14

certified_graph_case record025 30 1026711093248 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10535 14

certified_graph_case record026 30 1026843213824 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10536 14

certified_graph_case record027 30 1042135679232 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10537 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00001

module
prelude
public meta import GraphCases
public import GraphInputsRow23Part00020Checked
public import GraphInputsRow23Part00020Metadata
public import GraphInputsRow23Part00020Frames
public import GraphInputsRow23Part00020Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch056
public import GraphInputsRow23Part00020Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00020
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 23 27267812065280 GraphCoverageDescriptions.GraphCoverageBatch056.candidate05622 6

certified_graph_case record001 23 27268080467968 GraphCoverageDescriptions.GraphCoverageBatch056.candidate05623 6

certified_graph_case record002 23 27354179076096 GraphCoverageDescriptions.GraphCoverageBatch056.candidate05624 6

certified_graph_case record003 23 27386877870336 GraphCoverageDescriptions.GraphCoverageBatch056.candidate05625 6

certified_graph_case record004 23 27387414740992 GraphCoverageDescriptions.GraphCoverageBatch056.candidate05626 6

certified_graph_case record005 23 27493740322944 GraphCoverageDescriptions.GraphCoverageBatch056.candidate05627 6

certified_graph_case record006 23 27561367707776 GraphCoverageDescriptions.GraphCoverageBatch056.candidate05628 6

certified_graph_case record007 23 27566980219136 GraphCoverageDescriptions.GraphCoverageBatch056.candidate05629 6

certified_graph_case record008 23 27602290999296 GraphCoverageDescriptions.GraphCoverageBatch056.candidate05630 6

certified_graph_case record009 23 27602414796800 GraphCoverageDescriptions.GraphCoverageBatch056.candidate05631 6

certified_graph_case record010 23 27671000055808 GraphCoverageDescriptions.GraphCoverageBatch056.candidate05632 6

certified_graph_case record011 23 27685428412672 GraphCoverageDescriptions.GraphCoverageBatch056.candidate05633 6

certified_graph_case record012 23 27747774693376 GraphCoverageDescriptions.GraphCoverageBatch056.candidate05634 6

certified_graph_case record013 23 27748443619328 GraphCoverageDescriptions.GraphCoverageBatch056.candidate05635 6

certified_graph_case record014 23 27756368756736 GraphCoverageDescriptions.GraphCoverageBatch056.candidate05636 6

theorem record015_parameters : Parameters record015 (rowOfCode 23) 27756897239040 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record015_coverage : Coverage record015 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 27756897239040 :=
  GraphCoverageDescriptions.coverage_of_checked record015 GraphCoverageDescriptions.GraphCoverageBatch056.candidate05637 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 27756897239040
    (by rfl) record015_cells_exact
    (GraphCoverageDescriptions.small_allowed record015 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch056.candidate05637_checked

theorem record015_result : Result (23, 27756897239040) :=
  of_direct_small 23 27756897239040 (by decide) ⟨record015, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00020.record015.direct_core, record015_parameters, record015_coverage⟩

theorem record016_parameters : Parameters record016 (rowOfCode 23) 27802602635264 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record016_coverage : Coverage record016 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 27802602635264 :=
  GraphCoverageDescriptions.coverage_of_checked record016 GraphCoverageDescriptions.GraphCoverageBatch056.candidate05638 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 27802602635264
    (by rfl) record016_cells_exact
    (GraphCoverageDescriptions.small_allowed record016 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch056.candidate05638_checked

theorem record016_result : Result (23, 27802602635264) :=
  of_direct_small 23 27802602635264 (by decide) ⟨record016, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00020.record016.direct_core, record016_parameters, record016_coverage⟩

theorem record017_parameters : Parameters record017 (rowOfCode 23) 27941320785920 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record017_coverage : Coverage record017 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 27941320785920 :=
  GraphCoverageDescriptions.coverage_of_checked record017 GraphCoverageDescriptions.GraphCoverageBatch056.candidate05639 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 27941320785920
    (by rfl) record017_cells_exact
    (GraphCoverageDescriptions.small_allowed record017 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch056.candidate05639_checked

theorem record017_result : Result (23, 27941320785920) :=
  of_direct_small 23 27941320785920 (by decide) ⟨record017, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00020.record017.direct_core, record017_parameters, record017_coverage⟩

certified_graph_case record018 23 27945341091840 GraphCoverageDescriptions.GraphCoverageBatch056.candidate05640 6

certified_graph_case record019 23 27947421466624 GraphCoverageDescriptions.GraphCoverageBatch056.candidate05641 6

certified_graph_case record020 23 28076495339521 GraphCoverageDescriptions.GraphCoverageBatch056.candidate05642 6
end Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00020

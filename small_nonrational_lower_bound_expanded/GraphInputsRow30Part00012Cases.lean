module
prelude
public meta import GraphCases
public import GraphInputsRow30Part00012Checked
public import GraphInputsRow30Part00012Metadata
public import GraphInputsRow30Part00012Frames
public import GraphInputsRow30Part00012Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch108
public import GraphInputsRow30Part00012Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00012
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 30 7003355217920 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10867 14

certified_graph_case record001 30 7003619459072 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10868 14

certified_graph_case record002 30 7003883700224 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10869 14

certified_graph_case record003 30 7048242954496 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10870 14

certified_graph_case record004 30 7050864164864 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10871 14

certified_graph_case record005 30 7098039566336 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10872 14

certified_graph_case record006 30 7150227194112 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10873 14

certified_graph_case record007 30 7150227259392 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10874 14

certified_graph_case record008 30 7150359379968 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10875 14

theorem record009_parameters : Parameters record009 (rowOfCode 30) 7150462046464 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 7150462046464 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10876 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 7150462046464
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.small_allowed record009 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch108.candidate10876_checked

theorem record009_result : Result (30, 7150462046464) :=
  of_direct_small 30 7150462046464 (by decide) ⟨record009, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00012.record009.direct_core, record009_parameters, record009_coverage⟩

certified_graph_case record010 30 7154085924880 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10877 14

certified_graph_case record011 30 7156800765952 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10878 14

certified_graph_case record012 30 7156901351680 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10879 14

certified_graph_case record013 30 7157062926336 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10880 14

certified_graph_case record014 30 7157065007104 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10881 14

certified_graph_case record015 30 7158246674448 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10882 14

certified_graph_case record016 30 7165421031680 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10883 14

certified_graph_case record017 30 7185774510080 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10884 14

certified_graph_case record018 30 7185778086144 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10885 14

certified_graph_case record019 30 7186298177552 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10886 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00012

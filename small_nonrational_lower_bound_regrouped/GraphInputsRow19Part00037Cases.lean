module
prelude
public meta import GraphCases
public import GraphInputsRow19Part00037Checked
public import GraphInputsRow19Part00037Metadata
public import GraphInputsRow19Part00037Frames
public import GraphInputsRow19Part00037Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch020
public import GraphCoverageBatch039
public import GraphInputsRow19Part00037Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 19 34682415091712 GraphCoverageDescriptions.GraphCoverageBatch020.candidate02091 14

certified_graph_case record001 19 34682431606784 GraphCoverageDescriptions.GraphCoverageBatch020.candidate02092 14

certified_graph_case record002 19 34682934792448 GraphCoverageDescriptions.GraphCoverageBatch039.candidate03908 14

certified_graph_case record003 19 34682968408064 GraphCoverageDescriptions.GraphCoverageBatch020.candidate02093 14

certified_graph_case record004 19 34682976731136 GraphCoverageDescriptions.GraphCoverageBatch020.candidate02094 14

certified_graph_case record005 19 34683471663104 GraphCoverageDescriptions.GraphCoverageBatch020.candidate02095 14

certified_graph_case record006 19 34683505082880 GraphCoverageDescriptions.GraphCoverageBatch020.candidate02096 14

certified_graph_case record007 19 34699074473984 GraphCoverageDescriptions.GraphCoverageBatch039.candidate03909 14

certified_graph_case record008 19 34699074994176 GraphCoverageDescriptions.GraphCoverageBatch039.candidate03910 14

certified_graph_case record009 19 34737746116864 GraphCoverageDescriptions.GraphCoverageBatch039.candidate03911 14

certified_graph_case record010 19 34737750343680 GraphCoverageDescriptions.GraphCoverageBatch039.candidate03912 14

certified_graph_case record011 19 34737758406656 GraphCoverageDescriptions.GraphCoverageBatch039.candidate03913 14

certified_graph_case record012 19 34737980969216 GraphCoverageDescriptions.GraphCoverageBatch039.candidate03914 14

certified_graph_case record013 19 34737989357568 GraphCoverageDescriptions.GraphCoverageBatch039.candidate03915 14

certified_graph_case record014 19 34737989617664 GraphCoverageDescriptions.GraphCoverageBatch039.candidate03916 14

certified_graph_case record015 19 34737997744384 GraphCoverageDescriptions.GraphCoverageBatch039.candidate03917 14

certified_graph_case record016 19 34739037800704 GraphCoverageDescriptions.GraphCoverageBatch039.candidate03918 14

certified_graph_case record017 19 34739046189056 GraphCoverageDescriptions.GraphCoverageBatch039.candidate03919 14

theorem record018_parameters : Parameters record018 (rowOfCode 19) 34739054445312 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record018_coverage : Coverage record018 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34739054445312 :=
  GraphCoverageDescriptions.coverage_of_checked record018 GraphCoverageDescriptions.GraphCoverageBatch039.candidate03920 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 34739054445312
    (by rfl) record018_cells_exact
    (GraphCoverageDescriptions.small_allowed record018 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch039.candidate03920_checked

theorem record018_result : Result (19, 34739054445312) :=
  of_direct_small 19 34739054445312 (by decide) ⟨record018, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00037.record018.direct_core, record018_parameters, record018_coverage⟩
#print axioms record018_result

certified_graph_case record019 19 34746327500800 GraphCoverageDescriptions.GraphCoverageBatch039.candidate03921 14

certified_graph_case record020 19 34746822428688 GraphCoverageDescriptions.GraphCoverageBatch039.candidate03922 14

certified_graph_case record021 19 34746839073296 GraphCoverageDescriptions.GraphCoverageBatch039.candidate03923 14

certified_graph_case record022 19 34746855850504 GraphCoverageDescriptions.GraphCoverageBatch039.candidate03924 14

theorem record023_parameters : Parameters record023 (rowOfCode 19) 34763465426960 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record023_coverage : Coverage record023 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34763465426960 :=
  GraphCoverageDescriptions.coverage_of_checked record023 GraphCoverageDescriptions.GraphCoverageBatch039.candidate03925 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 34763465426960
    (by rfl) record023_cells_exact
    (GraphCoverageDescriptions.small_allowed record023 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch039.candidate03925_checked

theorem record023_result : Result (19, 34763465426960) :=
  of_direct_small 19 34763465426960 (by decide) ⟨record023, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00037.record023.direct_core, record023_parameters, record023_coverage⟩
#print axioms record023_result

certified_graph_case record024 19 34763482206208 GraphCoverageDescriptions.GraphCoverageBatch039.candidate03926 14

certified_graph_case record025 19 34763482726400 GraphCoverageDescriptions.GraphCoverageBatch020.candidate02097 14

certified_graph_case record026 19 34763515625984 GraphCoverageDescriptions.GraphCoverageBatch039.candidate03927 14

certified_graph_case record027 19 34764539036164 GraphCoverageDescriptions.GraphCoverageBatch039.candidate03928 14

certified_graph_case record028 19 34764539167744 GraphCoverageDescriptions.GraphCoverageBatch039.candidate03929 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00037

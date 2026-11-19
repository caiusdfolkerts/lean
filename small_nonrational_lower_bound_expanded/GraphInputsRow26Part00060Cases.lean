module
prelude
public meta import GraphCases
public import GraphInputsRow26Part00060Checked
public import GraphInputsRow26Part00060Metadata
public import GraphInputsRow26Part00060Frames
public import GraphInputsRow26Part00060Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch097
public import GraphCoverageBatch098
public import GraphCoverageBatch129
public import GraphInputsRow26Part00060Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00060
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 26 28865574518784 GraphCoverageDescriptions.GraphCoverageBatch097.candidate09783 14

certified_graph_case record001 26 28869799215232 GraphCoverageDescriptions.GraphCoverageBatch097.candidate09784 14

certified_graph_case record002 26 28869803409408 GraphCoverageDescriptions.GraphCoverageBatch097.candidate09785 14

certified_graph_case record003 26 28869999476864 GraphCoverageDescriptions.GraphCoverageBatch097.candidate09786 14

certified_graph_case record004 26 28874162339840 GraphCoverageDescriptions.GraphCoverageBatch097.candidate09787 14

certified_graph_case record005 26 28897767882880 GraphCoverageDescriptions.GraphCoverageBatch097.candidate09789 14

certified_graph_case record006 26 28897769963648 GraphCoverageDescriptions.GraphCoverageBatch097.candidate09790 14

certified_graph_case record007 26 28897769996288 GraphCoverageDescriptions.GraphCoverageBatch097.candidate09791 14

certified_graph_case record008 26 28900941891712 GraphCoverageDescriptions.GraphCoverageBatch129.candidate12975 14

certified_graph_case record009 26 28900990689280 GraphCoverageDescriptions.GraphCoverageBatch097.candidate09793 14

certified_graph_case record010 26 28901007952000 GraphCoverageDescriptions.GraphCoverageBatch097.candidate09794 14

certified_graph_case record011 26 28901121736832 GraphCoverageDescriptions.GraphCoverageBatch129.candidate12976 14

certified_graph_case record012 26 28901121769472 GraphCoverageDescriptions.GraphCoverageBatch097.candidate09795 14

certified_graph_case record013 26 28901122809856 GraphCoverageDescriptions.GraphCoverageBatch097.candidate09796 14

certified_graph_case record014 26 28932062593152 GraphCoverageDescriptions.GraphCoverageBatch097.candidate09799 14

certified_graph_case record015 26 28933135810688 GraphCoverageDescriptions.GraphCoverageBatch129.candidate12977 14

theorem record016_parameters : Parameters record016 (rowOfCode 26) 28933333991552 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record016_coverage : Coverage record016 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 28933333991552 :=
  GraphCoverageDescriptions.coverage_of_checked record016 GraphCoverageDescriptions.GraphCoverageBatch098.candidate09800 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 28933333991552
    (by rfl) record016_cells_exact
    (GraphCoverageDescriptions.small_allowed record016 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch098.candidate09800_checked

theorem record016_result : Result (26, 28933333991552) :=
  of_direct_small 26 28933333991552 (by decide) ⟨record016, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00060.record016.direct_core, record016_parameters, record016_coverage⟩

certified_graph_case record017 26 28965345722496 GraphCoverageDescriptions.GraphCoverageBatch129.candidate12978 14

certified_graph_case record018 26 28965347803264 GraphCoverageDescriptions.GraphCoverageBatch129.candidate12979 14

certified_graph_case record019 26 28965347835904 GraphCoverageDescriptions.GraphCoverageBatch098.candidate09801 14

certified_graph_case record020 26 28965349623936 GraphCoverageDescriptions.GraphCoverageBatch129.candidate12980 14

certified_graph_case record021 26 28965547804800 GraphCoverageDescriptions.GraphCoverageBatch129.candidate12981 14

certified_graph_case record022 26 28965549137920 GraphCoverageDescriptions.GraphCoverageBatch098.candidate09802 14

certified_graph_case record023 26 28965601282056 GraphCoverageDescriptions.GraphCoverageBatch129.candidate12982 14

theorem record024_parameters : Parameters record024 (rowOfCode 26) 28967545473152 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record024_coverage : Coverage record024 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 28967545473152 :=
  GraphCoverageDescriptions.coverage_of_checked record024 GraphCoverageDescriptions.GraphCoverageBatch129.candidate12983 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 28967545473152
    (by rfl) record024_cells_exact
    (GraphCoverageDescriptions.small_allowed record024 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch129.candidate12983_checked

theorem record024_result : Result (26, 28967545473152) :=
  of_direct_small 26 28967545473152 (by decide) ⟨record024, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00060.record024.direct_core, record024_parameters, record024_coverage⟩

theorem record025_parameters : Parameters record025 (rowOfCode 26) 28967545505792 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record025_coverage : Coverage record025 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 28967545505792 :=
  GraphCoverageDescriptions.coverage_of_checked record025 GraphCoverageDescriptions.GraphCoverageBatch098.candidate09803 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 28967545505792
    (by rfl) record025_cells_exact
    (GraphCoverageDescriptions.small_allowed record025 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch098.candidate09803_checked

theorem record025_result : Result (26, 28967545505792) :=
  of_direct_small 26 28967545505792 (by decide) ⟨record025, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00060.record025.direct_core, record025_parameters, record025_coverage⟩

certified_graph_case record026 26 28967562150400 GraphCoverageDescriptions.GraphCoverageBatch129.candidate12984 14

certified_graph_case record027 26 28967681655816 GraphCoverageDescriptions.GraphCoverageBatch129.candidate12985 14

certified_graph_case record028 26 28967698432001 GraphCoverageDescriptions.GraphCoverageBatch129.candidate12986 14

certified_graph_case record029 26 28974120961032 GraphCoverageDescriptions.GraphCoverageBatch129.candidate12987 14

certified_graph_case record030 26 28974137737217 GraphCoverageDescriptions.GraphCoverageBatch129.candidate12988 14

certified_graph_case record031 26 29001937586304 GraphCoverageDescriptions.GraphCoverageBatch098.candidate09805 14

certified_graph_case record032 26 29034133063808 GraphCoverageDescriptions.GraphCoverageBatch129.candidate12989 14

certified_graph_case record033 26 29036262852736 GraphCoverageDescriptions.GraphCoverageBatch129.candidate12990 14

theorem record034_parameters : Parameters record034 (rowOfCode 26) 29038343227520 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record034_coverage : Coverage record034 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29038343227520 :=
  GraphCoverageDescriptions.coverage_of_checked record034 GraphCoverageDescriptions.GraphCoverageBatch129.candidate12991 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 29038343227520
    (by rfl) record034_cells_exact
    (GraphCoverageDescriptions.small_allowed record034 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch129.candidate12991_checked

theorem record034_result : Result (26, 29038343227520) :=
  of_direct_small 26 29038343227520 (by decide) ⟨record034, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00060.record034.direct_core, record034_parameters, record034_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00060

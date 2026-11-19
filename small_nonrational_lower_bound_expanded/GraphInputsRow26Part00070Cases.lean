module
prelude
public meta import GraphCases
public import GraphInputsRow26Part00070Checked
public import GraphInputsRow26Part00070Metadata
public import GraphInputsRow26Part00070Frames
public import GraphInputsRow26Part00070Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch100
public import GraphCoverageBatch101
public import GraphCoverageBatch130
public import GraphInputsRow26Part00070Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 26 31785060728832 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10097 14

certified_graph_case record001 26 31785069051904 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10098 14

certified_graph_case record002 26 31785308454912 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10099 14

certified_graph_case record003 26 31787070816512 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10100 14

certified_graph_case record004 26 31787339284480 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10101 14

certified_graph_case record005 26 31787347607552 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10102 14

certified_graph_case record006 26 31787388829696 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10103 14

certified_graph_case record007 26 31787858534400 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10104 14

certified_graph_case record008 26 31812822900736 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10108 14

theorem record009_parameters : Parameters record009 (rowOfCode 26) 31812890001408 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31812890001408 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10109 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 31812890001408
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.small_allowed record009 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch101.candidate10109_checked

theorem record009_result : Result (26, 31812890001408) :=
  of_direct_small 26 31812890001408 (by decide) ⟨record009, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00070.record009.direct_core, record009_parameters, record009_coverage⟩

certified_graph_case record010 26 31819283071232 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10110 14

certified_graph_case record011 26 31819353358336 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10111 14

theorem record012_parameters : Parameters record012 (rowOfCode 26) 31819361681408 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record012_coverage : Coverage record012 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31819361681408 :=
  GraphCoverageDescriptions.coverage_of_checked record012 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10112 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 31819361681408
    (by rfl) record012_cells_exact
    (GraphCoverageDescriptions.small_allowed record012 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch101.candidate10112_checked

theorem record012_result : Result (26, 31819361681408) :=
  of_direct_small 26 31819361681408 (by decide) ⟨record012, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00070.record012.direct_core, record012_parameters, record012_coverage⟩

certified_graph_case record013 26 31819551539200 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10113 14

certified_graph_case record014 26 31819559862272 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10114 14

certified_graph_case record015 26 31819601084416 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10115 14

certified_graph_case record016 26 31820070789120 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10116 14

certified_graph_case record017 26 31825725497600 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10117 14

certified_graph_case record018 26 31826262368256 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10118 14

certified_graph_case record019 26 31826311913472 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10119 14

certified_graph_case record020 26 31827855286528 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10120 14

certified_graph_case record021 26 31828459127296 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10121 14

certified_graph_case record022 26 31842887671840 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10122 14

certified_graph_case record023 26 31887070953504 GraphCoverageDescriptions.GraphCoverageBatch130.candidate13068 14

certified_graph_case record024 26 31887205154848 GraphCoverageDescriptions.GraphCoverageBatch130.candidate13069 14

certified_graph_case record025 26 31889171693824 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10123 14

certified_graph_case record026 26 31890426368032 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10127 14

theorem record027_parameters : Parameters record027 (rowOfCode 26) 31890690609184 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record027_coverage : Coverage record027 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31890690609184 :=
  GraphCoverageDescriptions.coverage_of_checked record027 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10128 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 31890690609184
    (by rfl) record027_cells_exact
    (GraphCoverageDescriptions.small_allowed record027 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch101.candidate10128_checked

theorem record027_result : Result (26, 31890690609184) :=
  of_direct_small 26 31890690609184 (by decide) ⟨record027, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00070.record027.direct_core, record027_parameters, record027_coverage⟩

certified_graph_case record028 26 31891386278144 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10129 14

certified_graph_case record029 26 31891482939424 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10130 14

certified_graph_case record030 26 31891751342112 GraphCoverageDescriptions.GraphCoverageBatch130.candidate13070 14

certified_graph_case record031 26 31904435802176 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10132 14

certified_graph_case record032 26 31922638569728 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10133 14

certified_graph_case record033 26 31922910662720 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10134 14

certified_graph_case record034 26 31926237823232 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10136 14

certified_graph_case record035 26 31929349967936 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10138 14

certified_graph_case record036 26 31994901692416 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10143 14

certified_graph_case record037 26 31995091550208 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10144 14

certified_graph_case record038 26 32011536367616 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10145 14

certified_graph_case record039 26 32011808931840 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10146 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00070

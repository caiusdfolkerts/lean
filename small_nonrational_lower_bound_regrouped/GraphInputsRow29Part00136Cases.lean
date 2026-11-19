module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00136Checked
public import GraphInputsRow29Part00136Metadata
public import GraphInputsRow29Part00136Frames
public import GraphInputsRow29Part00136Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch117
public import GraphCoverageBatch150
public import GraphCoverageBatch151
public import GraphInputsRow29Part00136Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 23383288848384 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15099 14

certified_graph_case record001 29 23383485988864 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15100 14

certified_graph_case record002 29 23383682072640 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15101 14

certified_graph_case record003 29 23386902765632 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15102 14

certified_graph_case record004 29 23412537819904 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15103 14

certified_graph_case record005 29 23418445529344 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15104 14

certified_graph_case record006 29 23418713997312 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15105 14

certified_graph_case record007 29 23419116601344 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11702 14

certified_graph_case record008 29 23420525904128 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15106 14

certified_graph_case record009 29 23421263036416 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11703 14

certified_graph_case record010 29 23424820855040 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11704 14

certified_graph_case record011 29 23469987266816 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15107 14

certified_graph_case record012 29 23474420645888 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15108 14

certified_graph_case record013 29 23474957451264 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11705 14

certified_graph_case record014 29 23478581395456 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15109 14

certified_graph_case record015 29 23479118200832 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15110 14

certified_graph_case record016 29 23487167135744 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15111 14

certified_graph_case record017 29 23487836061696 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11706 14

certified_graph_case record018 29 23493540380672 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11707 14

theorem record019_parameters : Parameters record019 (rowOfCode 29) 23495761199104 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record019_coverage : Coverage record019 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 23495761199104 :=
  GraphCoverageDescriptions.coverage_of_checked record019 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11708 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 23495761199104
    (by rfl) record019_cells_exact
    (GraphCoverageDescriptions.small_allowed record019 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch117.candidate11708_checked

theorem record019_result : Result (29, 23495761199104) :=
  of_direct_small 29 23495761199104 (by decide) ⟨record019, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00136.record019.direct_core, record019_parameters, record019_coverage⟩
#print axioms record019_result

theorem record020_parameters : Parameters record020 (rowOfCode 29) 23496289681408 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record020_coverage : Coverage record020 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 23496289681408 :=
  GraphCoverageDescriptions.coverage_of_checked record020 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11709 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 23496289681408
    (by rfl) record020_cells_exact
    (GraphCoverageDescriptions.small_allowed record020 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch117.candidate11709_checked

theorem record020_result : Result (29, 23496289681408) :=
  of_direct_small 29 23496289681408 (by decide) ⟨record020, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00136.record020.direct_core, record020_parameters, record020_coverage⟩
#print axioms record020_result

certified_graph_case record021 29 23538704646400 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11710 14

certified_graph_case record022 29 23543005904896 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11711 14

certified_graph_case record023 29 23543542710272 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11712 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00136

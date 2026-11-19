module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00168Checked
public import GraphInputsRow29Part00168Metadata
public import GraphInputsRow29Part00168Frames
public import GraphInputsRow29Part00168Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch118
public import GraphCoverageBatch152
public import GraphInputsRow29Part00168Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00168
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 25574418432256 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15255 14

certified_graph_case record001 29 25575054393344 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15256 14

certified_graph_case record002 29 25576564867328 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11836 14

certified_graph_case record003 29 25582106574848 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11837 14

certified_graph_case record004 29 25582236614656 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15257 14

certified_graph_case record005 29 25582302674944 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11838 14

theorem record006_parameters : Parameters record006 (rowOfCode 29) 25583375892480 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25583375892480 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11839 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25583375892480
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch118.candidate11839_checked

theorem record006_result : Result (29, 25583375892480) :=
  of_direct_small 29 25583375892480 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00168.record006.direct_core, record006_parameters, record006_coverage⟩

certified_graph_case record007 29 25589449769024 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15258 14

theorem record008_parameters : Parameters record008 (rowOfCode 29) 25610890133760 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25610890133760 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15259 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25610890133760
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch152.candidate15259_checked

theorem record008_result : Result (29, 25610890133760) :=
  of_direct_small 29 25610890133760 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00168.record008.direct_core, record008_parameters, record008_coverage⟩

certified_graph_case record009 29 25611561075200 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15260 14

certified_graph_case record010 29 25623775035456 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15261 14

certified_graph_case record011 29 25642097770496 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11840 14

certified_graph_case record012 29 25658134765632 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15262 14

certified_graph_case record013 29 25659277574144 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11841 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00168

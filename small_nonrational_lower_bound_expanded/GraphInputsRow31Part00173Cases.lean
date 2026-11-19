module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00173Checked
public import GraphInputsRow31Part00173Metadata
public import GraphInputsRow31Part00173Frames
public import GraphInputsRow31Part00173Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch168
public import GraphCoverageBatch169
public import GraphInputsRow31Part00173Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 34256678092800 GraphCoverageDescriptions.GraphCoverageBatch168.candidate16897 14

certified_graph_case record001 31 34278134120448 GraphCoverageDescriptions.GraphCoverageBatch168.candidate16898 14

certified_graph_case record002 31 34497177454656 GraphCoverageDescriptions.GraphCoverageBatch168.candidate16899 14

certified_graph_case record003 31 34497195163648 GraphCoverageDescriptions.GraphCoverageBatch169.candidate16900 14

certified_graph_case record004 31 34498320269312 GraphCoverageDescriptions.GraphCoverageBatch169.candidate16901 14

certified_graph_case record005 31 34500532764672 GraphCoverageDescriptions.GraphCoverageBatch169.candidate16902 14

certified_graph_case record006 31 34531555934208 GraphCoverageDescriptions.GraphCoverageBatch169.candidate16903 14

certified_graph_case record007 31 34535848804352 GraphCoverageDescriptions.GraphCoverageBatch169.candidate16904 14

certified_graph_case record008 31 34634633318416 GraphCoverageDescriptions.GraphCoverageBatch169.candidate16905 14

certified_graph_case record009 31 34634633580800 GraphCoverageDescriptions.GraphCoverageBatch169.candidate16906 14

certified_graph_case record010 31 34634633609472 GraphCoverageDescriptions.GraphCoverageBatch169.candidate16907 14

theorem record011_parameters : Parameters record011 (rowOfCode 31) 34634666872832 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record011_coverage : Coverage record011 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34634666872832 :=
  GraphCoverageDescriptions.coverage_of_checked record011 GraphCoverageDescriptions.GraphCoverageBatch169.candidate16908 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 34634666872832
    (by rfl) record011_cells_exact
    (GraphCoverageDescriptions.small_allowed record011 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch169.candidate16908_checked

theorem record011_result : Result (31, 34634666872832) :=
  of_direct_small 31 34634666872832 (by decide) ⟨record011, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00173.record011.direct_core, record011_parameters, record011_coverage⟩

theorem record012_parameters : Parameters record012 (rowOfCode 31) 34634667393024 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record012_coverage : Coverage record012 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34634667393024 :=
  GraphCoverageDescriptions.coverage_of_checked record012 GraphCoverageDescriptions.GraphCoverageBatch169.candidate16909 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 34634667393024
    (by rfl) record012_cells_exact
    (GraphCoverageDescriptions.small_allowed record012 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch169.candidate16909_checked

theorem record012_result : Result (31, 34634667393024) :=
  of_direct_small 31 34634667393024 (by decide) ⟨record012, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00173.record012.direct_core, record012_parameters, record012_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173

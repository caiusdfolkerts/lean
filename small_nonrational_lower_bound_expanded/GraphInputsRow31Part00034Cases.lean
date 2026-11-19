module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00034Checked
public import GraphInputsRow31Part00034Metadata
public import GraphInputsRow31Part00034Frames
public import GraphInputsRow31Part00034Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch158
public import GraphCoverageBatch159
public import GraphInputsRow31Part00034Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00034
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 7295673630720 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15891 14

theorem record001_parameters : Parameters record001 (rowOfCode 31) 7297754005504 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 7297754005504 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15892 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 7297754005504
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch158.candidate15892_checked

theorem record001_result : Result (31, 7297754005504) :=
  of_direct_small 31 7297754005504 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00034.record001.direct_core, record001_parameters, record001_coverage⟩

certified_graph_case record002 31 7302587384064 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15893 14

certified_graph_case record003 31 7302723731456 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15894 14

certified_graph_case record004 31 7302732054528 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15895 14

certified_graph_case record005 31 7302864175104 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15896 14

theorem record006_parameters : Parameters record006 (rowOfCode 31) 7303627571456 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 7303627571456 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15897 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 7303627571456
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch158.candidate15897_checked

theorem record006_result : Result (31, 7303627571456) :=
  of_direct_small 31 7303627571456 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00034.record006.direct_core, record006_parameters, record006_coverage⟩

certified_graph_case record007 31 7331509371136 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15898 14

certified_graph_case record008 31 7340099272960 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15899 14

certified_graph_case record009 31 7340904415744 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15900 14

certified_graph_case record010 31 7340912803840 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15901 14

theorem record011_parameters : Parameters record011 (rowOfCode 31) 7372311527680 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record011_coverage : Coverage record011 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 7372311527680 :=
  GraphCoverageDescriptions.coverage_of_checked record011 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15902 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 7372311527680
    (by rfl) record011_cells_exact
    (GraphCoverageDescriptions.small_allowed record011 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch159.candidate15902_checked

theorem record011_result : Result (31, 7372311527680) :=
  of_direct_small 31 7372311527680 (by decide) ⟨record011, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00034.record011.direct_core, record011_parameters, record011_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00034

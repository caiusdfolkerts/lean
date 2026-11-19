module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00020Checked
public import GraphInputsRow31Part00020Metadata
public import GraphInputsRow31Part00020Frames
public import GraphInputsRow31Part00020Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch157
public import GraphInputsRow31Part00020Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00020
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 5104178569216 GraphCoverageDescriptions.GraphCoverageBatch157.candidate15786 14

theorem record001_parameters : Parameters record001 (rowOfCode 31) 5107521954048 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 5107521954048 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch157.candidate15787 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 5107521954048
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch157.candidate15787_checked

theorem record001_result : Result (31, 5107521954048) :=
  of_direct_small 31 5107521954048 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00020.record001.direct_core, record001_parameters, record001_coverage⟩

certified_graph_case record002 31 5137340891136 GraphCoverageDescriptions.GraphCoverageBatch157.candidate15788 14

certified_graph_case record003 31 5139066847488 GraphCoverageDescriptions.GraphCoverageBatch157.candidate15789 14

certified_graph_case record004 31 5141881160448 GraphCoverageDescriptions.GraphCoverageBatch157.candidate15790 14

theorem record005_parameters : Parameters record005 (rowOfCode 31) 5236370972928 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 5236370972928 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch157.candidate15791 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 5236370972928
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch157.candidate15791_checked

theorem record005_result : Result (31, 5236370972928) :=
  of_direct_small 31 5236370972928 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00020.record005.direct_core, record005_parameters, record005_coverage⟩

theorem record006_parameters : Parameters record006 (rowOfCode 31) 5241337577728 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 5241337577728 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch157.candidate15792 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 5241337577728
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch157.candidate15792_checked

theorem record006_result : Result (31, 5241337577728) :=
  of_direct_small 31 5241337577728 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00020.record006.direct_core, record006_parameters, record006_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00020

module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00031Checked
public import GraphInputsRow31Part00031Metadata
public import GraphInputsRow31Part00031Frames
public import GraphInputsRow31Part00031Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch158
public import GraphInputsRow31Part00031Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00031
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 31) 7191260102656 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 7191260102656 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15880 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 7191260102656
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch158.candidate15880_checked

theorem record000_result : Result (31, 7191260102656) :=
  of_direct_small 31 7191260102656 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00031.record000.direct_core, record000_parameters, record000_coverage⟩

theorem record001_parameters : Parameters record001 (rowOfCode 31) 7191524343808 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 7191524343808 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15881 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 7191524343808
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch158.candidate15881_checked

theorem record001_result : Result (31, 7191524343808) :=
  of_direct_small 31 7191524343808 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00031.record001.direct_core, record001_parameters, record001_coverage⟩

certified_graph_case record002 31 7191532666880 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15882 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00031

module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00007Checked
public import GraphInputsRow31Part00007Metadata
public import GraphInputsRow31Part00007Frames
public import GraphInputsRow31Part00007Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch156
public import GraphInputsRow31Part00007Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00007
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 31) 1255887872064 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 1255887872064 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15643 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 1255887872064
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch156.candidate15643_checked

theorem record000_result : Result (31, 1255887872064) :=
  of_direct_small 31 1255887872064 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00007.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 31 1289050145024 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15644 14

certified_graph_case record002 31 1289050210304 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15645 14

certified_graph_case record003 31 1289056436288 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15646 14

theorem record004_parameters : Parameters record004 (rowOfCode 31) 1293468827649 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 1293468827649 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15647 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 1293468827649
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch156.candidate15647_checked

theorem record004_result : Result (31, 1293468827649) :=
  of_direct_small 31 1293468827649 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00007.record004.direct_core, record004_parameters, record004_coverage⟩

certified_graph_case record005 31 1325681147904 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15648 14

theorem record006_parameters : Parameters record006 (rowOfCode 31) 1327817064704 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 1327817064704 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15649 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 1327817064704
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch156.candidate15649_checked

theorem record006_result : Result (31, 1327817064704) :=
  of_direct_small 31 1327817064704 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00007.record006.direct_core, record006_parameters, record006_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00007

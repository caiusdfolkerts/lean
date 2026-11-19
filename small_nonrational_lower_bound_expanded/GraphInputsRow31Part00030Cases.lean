module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00030Checked
public import GraphInputsRow31Part00030Metadata
public import GraphInputsRow31Part00030Frames
public import GraphInputsRow31Part00030Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch158
public import GraphInputsRow31Part00030Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00030
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 7035962802176 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15875 14

certified_graph_case record001 31 7186826723584 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15876 14

theorem record002_parameters : Parameters record002 (rowOfCode 31) 7187363594240 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 7187363594240 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15877 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 7187363594240
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch158.candidate15877_checked

theorem record002_result : Result (31, 7187363594240) :=
  of_direct_small 31 7187363594240 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00030.record002.direct_core, record002_parameters, record002_coverage⟩

certified_graph_case record003 31 7187371917312 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15878 14

theorem record004_parameters : Parameters record004 (rowOfCode 31) 7190987473152 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 7190987473152 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15879 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 7190987473152
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch158.candidate15879_checked

theorem record004_result : Result (31, 7190987473152) :=
  of_direct_small 31 7190987473152 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00030.record004.direct_core, record004_parameters, record004_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00030

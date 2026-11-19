module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00016Checked
public import GraphInputsRow31Part00016Metadata
public import GraphInputsRow31Part00016Frames
public import GraphInputsRow31Part00016Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch157
public import GraphInputsRow31Part00016Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00016
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 31) 3930700972032 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 3930700972032 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch157.candidate15725 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 3930700972032
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch157.candidate15725_checked

theorem record000_result : Result (31, 3930700972032) :=
  of_direct_small 31 3930700972032 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00016.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 31 3942815662336 GraphCoverageDescriptions.GraphCoverageBatch157.candidate15726 14

certified_graph_case record002 31 4059020984576 GraphCoverageDescriptions.GraphCoverageBatch157.candidate15727 14

certified_graph_case record003 31 4067334226176 GraphCoverageDescriptions.GraphCoverageBatch157.candidate15728 14

theorem record004_parameters : Parameters record004 (rowOfCode 31) 4075924128000 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 4075924128000 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch157.candidate15729 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 4075924128000
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch157.candidate15729_checked

theorem record004_result : Result (31, 4075924128000) :=
  of_direct_small 31 4075924128000 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00016.record004.direct_core, record004_parameters, record004_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00016

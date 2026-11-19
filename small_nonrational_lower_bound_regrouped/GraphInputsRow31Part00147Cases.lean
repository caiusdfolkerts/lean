module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00147Checked
public import GraphInputsRow31Part00147Metadata
public import GraphInputsRow31Part00147Frames
public import GraphInputsRow31Part00147Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch167
public import GraphInputsRow31Part00147Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00147
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 31) 30792030363904 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 30792030363904 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16741 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 30792030363904
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch167.candidate16741_checked

theorem record000_result : Result (31, 30792030363904) :=
  of_direct_small 31 30792030363904 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00147.record000.direct_core, record000_parameters, record000_coverage⟩
#print axioms record000_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00147

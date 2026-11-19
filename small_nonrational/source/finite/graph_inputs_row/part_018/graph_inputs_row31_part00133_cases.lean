module
prelude
public import GraphInputsRow31Part00133Checked
public import GraphInputsRow31Part00133Metadata
public import GraphInputsRow31Part00133Frames
public import GraphInputsRow31Part00133Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch166
public import GraphInputsRow31Part00133Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00133
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 31) 29418416275456 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29418416275456 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch166.candidate16689 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 29418416275456
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch166.candidate16689_checked

theorem record000_result : Result (31, 29418416275456) :=
  of_direct_small 31 29418416275456 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00133.record000.direct_core, record000_parameters, record000_coverage⟩
#print axioms record000_result

theorem record001_parameters : Parameters record001 (rowOfCode 31) 29422709145600 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29422709145600 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch166.candidate16690 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 29422709145600
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch166.candidate16690_checked

theorem record001_result : Result (31, 29422709145600) :=
  of_direct_small 31 29422709145600 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00133.record001.direct_core, record001_parameters, record001_coverage⟩
#print axioms record001_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00133

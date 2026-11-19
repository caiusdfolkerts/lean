module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00116Checked
public import GraphInputsRow31Part00116Metadata
public import GraphInputsRow31Part00116Frames
public import GraphInputsRow31Part00116Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch165
public import GraphInputsRow31Part00116Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00116
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 31) 26432919060480 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 26432919060480 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch165.candidate16585 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 26432919060480
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch165.candidate16585_checked

theorem record000_result : Result (31, 26432919060480) :=
  of_direct_small 31 26432919060480 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00116.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 31 26462708105216 GraphCoverageDescriptions.GraphCoverageBatch165.candidate16586 14

certified_graph_case record002 31 26466868854784 GraphCoverageDescriptions.GraphCoverageBatch165.candidate16587 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00116

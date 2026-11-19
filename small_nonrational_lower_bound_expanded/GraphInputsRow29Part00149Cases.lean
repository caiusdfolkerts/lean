module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00149Checked
public import GraphInputsRow29Part00149Metadata
public import GraphInputsRow29Part00149Frames
public import GraphInputsRow29Part00149Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch117
public import GraphInputsRow29Part00149Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00149
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 29) 24642785902592 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24642785902592 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11757 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24642785902592
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch117.candidate11757_checked

theorem record000_result : Result (29, 24642785902592) :=
  of_direct_small 29 24642785902592 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00149.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 29 24643182264320 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11758 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00149

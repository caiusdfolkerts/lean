module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00104Checked
public import GraphInputsRow31Part00104Metadata
public import GraphInputsRow31Part00104Frames
public import GraphInputsRow31Part00104Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch165
public import GraphInputsRow31Part00104Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00104
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 24190392475712 GraphCoverageDescriptions.GraphCoverageBatch165.candidate16500 14

theorem record001_parameters : Parameters record001 (rowOfCode 31) 24190623686720 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24190623686720 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch165.candidate16501 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24190623686720
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch165.candidate16501_checked

theorem record001_result : Result (31, 24190623686720) :=
  of_direct_small 31 24190623686720 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00104.record001.direct_core, record001_parameters, record001_coverage⟩

theorem record002_parameters : Parameters record002 (rowOfCode 31) 24194793373952 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24194793373952 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch165.candidate16502 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24194793373952
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch165.candidate16502_checked

theorem record002_result : Result (31, 24194793373952) :=
  of_direct_small 31 24194793373952 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00104.record002.direct_core, record002_parameters, record002_coverage⟩

certified_graph_case record003 31 24199490978048 GraphCoverageDescriptions.GraphCoverageBatch165.candidate16503 14

certified_graph_case record004 31 24208080912512 GraphCoverageDescriptions.GraphCoverageBatch165.candidate16504 14

certified_graph_case record005 31 24229189844992 GraphCoverageDescriptions.GraphCoverageBatch165.candidate16505 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00104

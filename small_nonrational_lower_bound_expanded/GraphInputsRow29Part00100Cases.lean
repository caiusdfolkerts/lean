module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00100Checked
public import GraphInputsRow29Part00100Metadata
public import GraphInputsRow29Part00100Frames
public import GraphInputsRow29Part00100Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch115
public import GraphInputsRow29Part00100Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00100
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 17198533836800 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11503 14

certified_graph_case record001 29 17198928101888 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11504 14

certified_graph_case record002 29 17201381834752 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11505 14

certified_graph_case record003 29 17202149851136 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11506 14

certified_graph_case record004 29 17205639123200 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11507 14

theorem record005_parameters : Parameters record005 (rowOfCode 29) 17218800779264 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 17218800779264 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11508 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 17218800779264
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch115.candidate11508_checked

theorem record005_result : Result (29, 17218800779264) :=
  of_direct_small 29 17218800779264 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00100.record005.direct_core, record005_parameters, record005_coverage⟩

certified_graph_case record006 29 17227659083776 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11509 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00100

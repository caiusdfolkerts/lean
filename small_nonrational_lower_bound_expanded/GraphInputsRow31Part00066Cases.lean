module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00066Checked
public import GraphInputsRow31Part00066Metadata
public import GraphInputsRow31Part00066Frames
public import GraphInputsRow31Part00066Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch161
public import GraphInputsRow31Part00066Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00066
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 13272867733504 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16123 14

certified_graph_case record001 31 13273127747840 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16124 14

certified_graph_case record002 31 13273139257344 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16125 14

theorem record003_parameters : Parameters record003 (rowOfCode 31) 13273329049856 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 13273329049856 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16126 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 13273329049856
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch161.candidate16126_checked

theorem record003_result : Result (31, 13273329049856) :=
  of_direct_small 31 13273329049856 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00066.record003.direct_core, record003_parameters, record003_coverage⟩

theorem record004_parameters : Parameters record004 (rowOfCode 31) 13274402267392 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 13274402267392 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16127 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 13274402267392
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch161.candidate16127_checked

theorem record004_result : Result (31, 13274402267392) :=
  of_direct_small 31 13274402267392 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00066.record004.direct_core, record004_parameters, record004_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00066

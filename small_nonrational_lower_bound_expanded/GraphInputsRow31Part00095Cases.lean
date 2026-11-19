module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00095Checked
public import GraphInputsRow31Part00095Metadata
public import GraphInputsRow31Part00095Frames
public import GraphInputsRow31Part00095Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch164
public import GraphInputsRow31Part00095Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00095
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 19328632160256 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16421 14

theorem record001_parameters : Parameters record001 (rowOfCode 31) 19366007701760 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 19366007701760 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16422 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 19366007701760
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch164.candidate16422_checked

theorem record001_result : Result (31, 19366007701760) :=
  of_direct_small 31 19366007701760 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00095.record001.direct_core, record001_parameters, record001_coverage⟩

certified_graph_case record002 31 19469900447744 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16423 14

certified_graph_case record003 31 19535390310976 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16424 14

certified_graph_case record004 31 19572841250816 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16425 14

certified_graph_case record005 31 19611625980416 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16426 14

theorem record006_parameters : Parameters record006 (rowOfCode 31) 19611628077056 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 19611628077056 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16427 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 19611628077056
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch164.candidate16427_checked

theorem record006_result : Result (31, 19611628077056) :=
  of_direct_small 31 19611628077056 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00095.record006.direct_core, record006_parameters, record006_coverage⟩

certified_graph_case record007 31 19623726612480 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16428 14

certified_graph_case record008 31 19624511143936 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16429 14

certified_graph_case record009 31 19641162268672 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16430 14

certified_graph_case record010 31 19679540297984 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16431 14

certified_graph_case record011 31 19878988759168 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16432 14

certified_graph_case record012 31 19947708235840 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16433 14

certified_graph_case record013 31 20019514736640 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16434 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00095

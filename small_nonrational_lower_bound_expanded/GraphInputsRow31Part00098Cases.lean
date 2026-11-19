module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00098Checked
public import GraphInputsRow31Part00098Metadata
public import GraphInputsRow31Part00098Frames
public import GraphInputsRow31Part00098Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch164
public import GraphInputsRow31Part00098Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00098
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 31) 21514565091584 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 21514565091584 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16451 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 21514565091584
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch164.candidate16451_checked

theorem record000_result : Result (31, 21514565091584) :=
  of_direct_small 31 21514565091584 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00098.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 31 21528125112320 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16452 14

certified_graph_case record002 31 21530708869120 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16453 14

certified_graph_case record003 31 21660065333248 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16454 14

certified_graph_case record004 31 21668386832384 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16455 14

certified_graph_case record005 31 21668915314688 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16456 14

certified_graph_case record006 31 21672547581952 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16457 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00098

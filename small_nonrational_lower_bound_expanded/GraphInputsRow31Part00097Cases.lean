module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00097Checked
public import GraphInputsRow31Part00097Metadata
public import GraphInputsRow31Part00097Frames
public import GraphInputsRow31Part00097Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch164
public import GraphInputsRow31Part00097Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00097
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 31) 20965014700032 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 20965014700032 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16446 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 20965014700032
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch164.candidate16446_checked

theorem record000_result : Result (31, 20965014700032) :=
  of_direct_small 31 20965014700032 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00097.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 31 21015950262272 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16447 14

certified_graph_case record002 31 21328807739456 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16448 14

certified_graph_case record003 31 21446017482752 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16449 14

certified_graph_case record004 31 21513508520192 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16450 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00097

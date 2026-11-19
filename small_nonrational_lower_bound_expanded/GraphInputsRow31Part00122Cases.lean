module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00122Checked
public import GraphInputsRow31Part00122Metadata
public import GraphInputsRow31Part00122Frames
public import GraphInputsRow31Part00122Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch166
public import GraphInputsRow31Part00122Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00122
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 27129299402752 GraphCoverageDescriptions.GraphCoverageBatch166.candidate16625 14

certified_graph_case record001 31 27132113715712 GraphCoverageDescriptions.GraphCoverageBatch166.candidate16626 14

certified_graph_case record002 31 27226603528192 GraphCoverageDescriptions.GraphCoverageBatch166.candidate16627 14

theorem record003_parameters : Parameters record003 (rowOfCode 31) 27238717210752 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 27238717210752 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch166.candidate16628 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 27238717210752
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch166.candidate16628_checked

theorem record003_result : Result (31, 27238717210752) :=
  of_direct_small 31 27238717210752 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00122.record003.direct_core, record003_parameters, record003_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00122

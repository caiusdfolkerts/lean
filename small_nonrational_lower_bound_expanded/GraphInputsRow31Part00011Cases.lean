module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00011Checked
public import GraphInputsRow31Part00011Metadata
public import GraphInputsRow31Part00011Frames
public import GraphInputsRow31Part00011Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch156
public import GraphCoverageBatch157
public import GraphInputsRow31Part00011Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00011
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 31) 2137023119360 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 2137023119360 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15697 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 2137023119360
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch156.candidate15697_checked

theorem record000_result : Result (31, 2137023119360) :=
  of_direct_small 31 2137023119360 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00011.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 31 2137559924736 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15698 14

certified_graph_case record002 31 2143801049088 GraphCoverageDescriptions.GraphCoverageBatch156.candidate15699 14

theorem record003_parameters : Parameters record003 (rowOfCode 31) 2149769609216 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 2149769609216 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch157.candidate15700 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 2149769609216
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch157.candidate15700_checked

theorem record003_result : Result (31, 2149769609216) :=
  of_direct_small 31 2149769609216 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00011.record003.direct_core, record003_parameters, record003_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00011

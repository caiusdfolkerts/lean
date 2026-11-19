module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00141Checked
public import GraphInputsRow31Part00141Metadata
public import GraphInputsRow31Part00141Frames
public import GraphInputsRow31Part00141Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch167
public import GraphInputsRow31Part00141Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00141
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 30249488809984 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16713 14

theorem record001_parameters : Parameters record001 (rowOfCode 31) 30254859059200 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 30254859059200 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16714 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 30254859059200
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch167.candidate16714_checked

theorem record001_result : Result (31, 30254859059200) :=
  of_direct_small 31 30254859059200 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00141.record001.direct_core, record001_parameters, record001_coverage⟩

certified_graph_case record002 31 30255226552320 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16715 14

theorem record003_parameters : Parameters record003 (rowOfCode 31) 30258078711808 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 30258078711808 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16716 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 30258078711808
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch167.candidate16716_checked

theorem record003_result : Result (31, 30258078711808) :=
  of_direct_small 31 30258078711808 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00141.record003.direct_core, record003_parameters, record003_coverage⟩

certified_graph_case record004 31 30305306575104 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16717 14

certified_graph_case record005 31 30313896542208 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16718 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00141

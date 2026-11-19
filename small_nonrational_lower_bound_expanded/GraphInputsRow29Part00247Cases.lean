module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00247Checked
public import GraphInputsRow29Part00247Metadata
public import GraphInputsRow29Part00247Frames
public import GraphInputsRow29Part00247Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch121
public import GraphInputsRow29Part00247Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00247
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 31995635761152 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12185 14

theorem record001_parameters : Parameters record001 (rowOfCode 29) 32010462625792 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32010462625792 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12186 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 32010462625792
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch121.candidate12186_checked

theorem record001_result : Result (29, 32010462625792) :=
  of_direct_small 29 32010462625792 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00247.record001.direct_core, record001_parameters, record001_coverage⟩

theorem record002_parameters : Parameters record002 (rowOfCode 29) 32028125307136 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32028125307136 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12187 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 32028125307136
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch121.candidate12187_checked

theorem record002_result : Result (29, 32028125307136) :=
  of_direct_small 29 32028125307136 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00247.record002.direct_core, record002_parameters, record002_coverage⟩

certified_graph_case record003 29 32041010208832 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12188 14

certified_graph_case record004 29 32041127383072 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12189 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00247

module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00286Checked
public import GraphInputsRow29Part00286Metadata
public import GraphInputsRow29Part00286Frames
public import GraphInputsRow29Part00286Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch123
public import GraphInputsRow29Part00286Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00286
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 29) 34640790814720 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34640790814720 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12336 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 34640790814720
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch123.candidate12336_checked

theorem record000_result : Result (29, 34640790814720) :=
  of_direct_small 29 34640790814720 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00286.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 29 34643223515392 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12337 14

certified_graph_case record002 29 34643760386048 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12338 14

theorem record003_parameters : Parameters record003 (rowOfCode 29) 34643776901120 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34643776901120 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12339 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 34643776901120
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch123.candidate12339_checked

theorem record003_result : Result (29, 34643776901120) :=
  of_direct_small 29 34643776901120 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00286.record003.direct_core, record003_parameters, record003_coverage⟩

certified_graph_case record004 29 34644280086784 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12340 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00286

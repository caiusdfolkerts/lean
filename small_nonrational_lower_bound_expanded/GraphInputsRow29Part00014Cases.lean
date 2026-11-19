module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00014Checked
public import GraphInputsRow29Part00014Metadata
public import GraphInputsRow29Part00014Frames
public import GraphInputsRow29Part00014Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch106
public import GraphInputsRow29Part00014Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00014
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 3629920583808 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10690 14

theorem record001_parameters : Parameters record001 (rowOfCode 29) 3647842877440 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 3647842877440 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10691 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 3647842877440
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch106.candidate10691_checked

theorem record001_result : Result (29, 3647842877440) :=
  of_direct_small 29 3647842877440 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00014.record001.direct_core, record001_parameters, record001_coverage⟩

certified_graph_case record002 29 3784067809536 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10692 14

theorem record003_parameters : Parameters record003 (rowOfCode 29) 3786689019904 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 3786689019904 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10693 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 3786689019904
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch106.candidate10693_checked

theorem record003_result : Result (29, 3786689019904) :=
  of_direct_small 29 3786689019904 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00014.record003.direct_core, record003_parameters, record003_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00014

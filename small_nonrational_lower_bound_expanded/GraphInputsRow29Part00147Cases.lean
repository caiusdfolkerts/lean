module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00147Checked
public import GraphInputsRow29Part00147Metadata
public import GraphInputsRow29Part00147Frames
public import GraphInputsRow29Part00147Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch117
public import GraphCoverageBatch151
public import GraphInputsRow29Part00147Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00147
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 24511781012224 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15180 14

certified_graph_case record001 29 24512183665216 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15181 14

certified_graph_case record002 29 24512184729600 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11752 14

theorem record003_parameters : Parameters record003 (rowOfCode 29) 24518229753856 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24518229753856 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15182 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24518229753856
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch151.candidate15182_checked

theorem record003_result : Result (29, 24518229753856) :=
  of_direct_small 29 24518229753856 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00147.record003.direct_core, record003_parameters, record003_coverage⟩

certified_graph_case record004 29 24521247555584 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11753 14

certified_graph_case record005 29 24569515671552 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15183 14

certified_graph_case record006 29 24570031800320 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15184 14

theorem record007_parameters : Parameters record007 (rowOfCode 29) 24572112175104 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24572112175104 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15185 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24572112175104
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch151.candidate15185_checked

theorem record007_result : Result (29, 24572112175104) :=
  of_direct_small 29 24572112175104 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00147.record007.direct_core, record007_parameters, record007_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00147

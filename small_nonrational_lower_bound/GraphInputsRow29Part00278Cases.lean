module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00278Checked
public import GraphInputsRow29Part00278Metadata
public import GraphInputsRow29Part00278Frames
public import GraphInputsRow29Part00278Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch122
public import GraphCoverageBatch123
public import GraphInputsRow29Part00278Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00278
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 34128884023552 GraphCoverageDescriptions.GraphCoverageBatch122.candidate12298 14

certified_graph_case record001 29 34129554964992 GraphCoverageDescriptions.GraphCoverageBatch122.candidate12299 14

certified_graph_case record002 29 34132105236736 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12300 14

theorem record003_parameters : Parameters record003 (rowOfCode 29) 34144990138432 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34144990138432 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12301 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 34144990138432
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch123.candidate12301_checked

theorem record003_result : Result (29, 34144990138432) :=
  of_direct_small 29 34144990138432 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00278.record003.direct_core, record003_parameters, record003_coverage⟩
#print axioms record003_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00278

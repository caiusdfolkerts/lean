module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00151Checked
public import GraphInputsRow24Part00151Metadata
public import GraphInputsRow24Part00151Frames
public import GraphInputsRow24Part00151Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch102
public import GraphInputsRow24Part00151Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 32514580153088 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10251 14

theorem record001_parameters : Parameters record001 (rowOfCode 24) 32521828176128 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32521828176128 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10252 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 32521828176128
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch102.candidate10252_checked

theorem record001_result : Result (24, 32521828176128) :=
  of_direct_small 24 32521828176128 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00151.record001.direct_core, record001_parameters, record001_coverage⟩
#print axioms record001_result

certified_graph_case record002 24 32522051260416 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10253 14

theorem record003_parameters : Parameters record003 (rowOfCode 24) 32522297937952 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32522297937952 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10254 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 32522297937952
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch102.candidate10254_checked

theorem record003_result : Result (24, 32522297937952) :=
  of_direct_small 24 32522297937952 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00151.record003.direct_core, record003_parameters, record003_coverage⟩
#print axioms record003_result

certified_graph_case record004 24 32522901652224 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10255 14

certified_graph_case record005 24 32523371414048 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10256 14

certified_graph_case record006 24 32524445155856 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10257 14

certified_graph_case record007 24 32531727515648 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10258 14

certified_graph_case record008 24 32642843083008 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10259 14

certified_graph_case record009 24 32642917531648 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10260 14

certified_graph_case record010 24 32643379953664 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10261 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00151

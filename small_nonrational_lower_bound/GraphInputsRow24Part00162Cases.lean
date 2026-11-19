module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00162Checked
public import GraphInputsRow24Part00162Metadata
public import GraphInputsRow24Part00162Frames
public import GraphInputsRow24Part00162Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch103
public import GraphInputsRow24Part00162Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00162
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 33206648700928 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10353 14

theorem record001_parameters : Parameters record001 (rowOfCode 24) 33207111122944 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 33207111122944 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10354 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 33207111122944
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch103.candidate10354_checked

theorem record001_result : Result (24, 33207111122944) :=
  of_direct_small 24 33207111122944 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00162.record001.direct_core, record001_parameters, record001_coverage⟩
#print axioms record001_result

certified_graph_case record002 24 33228417466368 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10355 14

certified_graph_case record003 24 33230448295936 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10356 14

certified_graph_case record004 24 33230456619008 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10357 14

certified_graph_case record005 24 33230497841152 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10358 14

certified_graph_case record006 24 33241436389376 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10359 14

certified_graph_case record007 24 33261385957504 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10360 14

certified_graph_case record008 24 33538634219520 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10361 14

certified_graph_case record009 24 33540780654592 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10362 14

certified_graph_case record010 24 33545073524736 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10363 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00162

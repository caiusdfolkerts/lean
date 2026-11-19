module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00016Checked
public import GraphInputsRow29Part00016Metadata
public import GraphInputsRow29Part00016Frames
public import GraphInputsRow29Part00016Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch107
public import GraphInputsRow29Part00016Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00016
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 3921599365120 GraphCoverageDescriptions.GraphCoverageBatch107.candidate10703 14

certified_graph_case record001 29 3921602941184 GraphCoverageDescriptions.GraphCoverageBatch107.candidate10704 14

certified_graph_case record002 29 3922123032592 GraphCoverageDescriptions.GraphCoverageBatch107.candidate10705 14

theorem record003_parameters : Parameters record003 (rowOfCode 29) 3922655871232 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 3922655871232 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch107.candidate10706 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 3922655871232
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch107.candidate10706_checked

theorem record003_result : Result (29, 3922655871232) :=
  of_direct_small 29 3922655871232 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00016.record003.direct_core, record003_parameters, record003_coverage⟩
#print axioms record003_result

certified_graph_case record004 29 3922655936512 GraphCoverageDescriptions.GraphCoverageBatch107.candidate10707 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00016

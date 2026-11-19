module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00172Checked
public import GraphInputsRow24Part00172Metadata
public import GraphInputsRow24Part00172Frames
public import GraphInputsRow24Part00172Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch104
public import GraphInputsRow24Part00172Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00172
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 34737712824576 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10461 14

certified_graph_case record001 24 34738790268928 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10462 14

certified_graph_case record002 24 34739062833152 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10463 14

theorem record003_parameters : Parameters record003 (rowOfCode 24) 34739574800384 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34739574800384 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10464 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 34739574800384
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch104.candidate10464_checked

theorem record003_result : Result (24, 34739574800384) :=
  of_direct_small 24 34739574800384 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00172.record003.direct_core, record003_parameters, record003_coverage⟩
#print axioms record003_result

certified_graph_case record004 24 34746302791680 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10465 14

certified_graph_case record005 24 34746839597056 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10466 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00172

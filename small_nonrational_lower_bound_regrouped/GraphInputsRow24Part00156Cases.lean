module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00156Checked
public import GraphInputsRow24Part00156Metadata
public import GraphInputsRow24Part00156Frames
public import GraphInputsRow24Part00156Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch102
public import GraphCoverageBatch103
public import GraphInputsRow24Part00156Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00156
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 32781069721600 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10297 14

certified_graph_case record001 24 32782411792640 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10298 14

theorem record002_parameters : Parameters record002 (rowOfCode 24) 32783216935424 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32783216935424 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10299 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 32783216935424
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch102.candidate10299_checked

theorem record002_result : Result (24, 32783216935424) :=
  of_direct_small 24 32783216935424 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00156.record002.direct_core, record002_parameters, record002_coverage⟩
#print axioms record002_result

certified_graph_case record003 24 32787797647616 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10300 14

certified_graph_case record004 24 32787881328640 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10301 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00156

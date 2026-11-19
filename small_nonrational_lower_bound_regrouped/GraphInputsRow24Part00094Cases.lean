module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00094Checked
public import GraphInputsRow24Part00094Metadata
public import GraphInputsRow24Part00094Frames
public import GraphInputsRow24Part00094Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch091
public import GraphInputsRow24Part00094Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00094
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 25153788446720 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09170 14

certified_graph_case record001 24 25154952364800 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09171 14

certified_graph_case record002 24 25155355017792 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09172 14

certified_graph_case record003 24 25156902780928 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09173 14

certified_graph_case record004 24 25160019362048 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09174 14

certified_graph_case record005 24 25160029571072 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09175 14

theorem record006_parameters : Parameters record006 (rowOfCode 24) 25160128661504 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25160128661504 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09176 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25160128661504
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch091.candidate09176_checked

theorem record006_result : Result (24, 25160128661504) :=
  of_direct_small 24 25160128661504 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00094.record006.direct_core, record006_parameters, record006_coverage⟩
#print axioms record006_result

certified_graph_case record007 24 25160472600640 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09177 14

certified_graph_case record008 24 25160473657344 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09178 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00094

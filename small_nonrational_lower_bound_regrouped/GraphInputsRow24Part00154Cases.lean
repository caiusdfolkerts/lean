module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00154Checked
public import GraphInputsRow24Part00154Metadata
public import GraphInputsRow24Part00154Frames
public import GraphInputsRow24Part00154Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch102
public import GraphInputsRow24Part00154Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00154
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 32716142739456 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10284 14

certified_graph_case record001 24 32717718684176 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10285 14

certified_graph_case record002 24 32725001043968 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10286 14

theorem record003_parameters : Parameters record003 (rowOfCode 24) 32728053714976 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32728053714976 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10287 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 32728053714976
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch102.candidate10287_checked

theorem record003_result : Result (24, 32728053714976) :=
  of_direct_small 24 32728053714976 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00154.record003.direct_core, record003_parameters, record003_coverage⟩
#print axioms record003_result

certified_graph_case record004 24 32729127191072 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10288 14

certified_graph_case record005 24 32730200932880 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10289 14

certified_graph_case record006 24 32748190367744 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10290 14

certified_graph_case record007 24 32780282003712 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10291 14

certified_graph_case record008 24 32780352290816 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10292 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00154

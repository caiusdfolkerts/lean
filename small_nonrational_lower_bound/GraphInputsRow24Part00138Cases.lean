module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00138Checked
public import GraphInputsRow24Part00138Metadata
public import GraphInputsRow24Part00138Frames
public import GraphInputsRow24Part00138Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch100
public import GraphInputsRow24Part00138Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00138
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 31761317765376 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10090 14

certified_graph_case record001 24 31763465306112 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10091 14

certified_graph_case record002 24 31763539689472 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10092 14

certified_graph_case record003 24 31764002111488 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10093 14

certified_graph_case record004 24 31778497634304 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10094 14

theorem record005_parameters : Parameters record005 (rowOfCode 24) 31778564734976 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31778564734976 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10095 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 31778564734976
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch100.candidate10095_checked

theorem record005_result : Result (24, 31778564734976) :=
  of_direct_small 24 31778564734976 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00138.record005.direct_core, record005_parameters, record005_coverage⟩
#print axioms record005_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00138

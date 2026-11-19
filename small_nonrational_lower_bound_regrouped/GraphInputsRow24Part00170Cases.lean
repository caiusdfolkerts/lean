module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00170Checked
public import GraphInputsRow24Part00170Metadata
public import GraphInputsRow24Part00170Frames
public import GraphInputsRow24Part00170Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch104
public import GraphInputsRow24Part00170Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00170
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 34673556783104 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10445 14

certified_graph_case record001 24 34673565106176 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10446 14

theorem record002_parameters : Parameters record002 (rowOfCode 24) 34674076553216 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34674076553216 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10447 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 34674076553216
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch104.candidate10447_checked

theorem record002_result : Result (24, 34674076553216) :=
  of_direct_small 24 34674076553216 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00170.record002.direct_core, record002_parameters, record002_coverage⟩
#print axioms record002_result

certified_graph_case record003 24 34674344886528 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10448 14

certified_graph_case record004 24 34674382536704 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10449 14

certified_graph_case record005 24 34674655100928 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10450 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00170

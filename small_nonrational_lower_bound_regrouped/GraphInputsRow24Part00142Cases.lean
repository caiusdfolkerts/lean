module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00142Checked
public import GraphInputsRow24Part00142Metadata
public import GraphInputsRow24Part00142Frames
public import GraphInputsRow24Part00142Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch101
public import GraphInputsRow24Part00142Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 32025986732096 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10149 14

certified_graph_case record001 24 32026600210688 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10150 14

theorem record002_parameters : Parameters record002 (rowOfCode 24) 32027077263360 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32027077263360 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10151 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 32027077263360
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch101.candidate10151_checked

theorem record002_result : Result (24, 32027077263360) :=
  of_direct_small 24 32027077263360 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00142.record002.direct_core, record002_parameters, record002_coverage⟩
#print axioms record002_result

certified_graph_case record003 24 32043780079616 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10152 14

certified_graph_case record004 24 32044316884992 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10153 14

certified_graph_case record005 24 32058795688192 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10154 14

certified_graph_case record006 24 32059272740864 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10155 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00142

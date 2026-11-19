module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00169Checked
public import GraphInputsRow24Part00169Metadata
public import GraphInputsRow24Part00169Frames
public import GraphInputsRow24Part00169Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch104
public import GraphInputsRow24Part00169Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00169
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 34638009532416 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10434 14

certified_graph_case record001 24 34638017855488 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10435 14

theorem record002_parameters : Parameters record002 (rowOfCode 24) 34638240743424 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34638240743424 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10436 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 34638240743424
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch104.candidate10436_checked

theorem record002_result : Result (24, 34638240743424) :=
  of_direct_small 24 34638240743424 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00169.record002.direct_core, record002_parameters, record002_coverage⟩
#print axioms record002_result

certified_graph_case record003 24 34639196983552 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10437 14

certified_graph_case record004 24 34639205371904 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10438 14

certified_graph_case record005 24 34639213498624 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10439 14

certified_graph_case record006 24 34640286974720 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10440 14

certified_graph_case record007 24 34641092837632 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10441 14

certified_graph_case record008 24 34641864560640 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10442 14

certified_graph_case record009 24 34670085439744 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10443 14

certified_graph_case record010 24 34673288315136 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10444 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00169

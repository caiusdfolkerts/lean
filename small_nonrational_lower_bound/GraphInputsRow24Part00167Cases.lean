module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00167Checked
public import GraphInputsRow24Part00167Metadata
public import GraphInputsRow24Part00167Frames
public import GraphInputsRow24Part00167Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch104
public import GraphInputsRow24Part00167Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00167
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 24) 34127952873488 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34127952873488 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10411 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 34127952873488
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch104.candidate10411_checked

theorem record000_result : Result (24, 34127952873488) :=
  of_direct_small 24 34127952873488 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00167.record000.direct_core, record000_parameters, record000_coverage⟩
#print axioms record000_result

certified_graph_case record001 24 34155878973696 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10412 14

certified_graph_case record002 24 34194419941376 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10413 14

certified_graph_case record003 24 34195732692992 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10414 14

certified_graph_case record004 24 34196261175296 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10415 14

certified_graph_case record005 24 34222385664256 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10416 14

certified_graph_case record006 24 34222391955520 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10417 14

certified_graph_case record007 24 34223424553216 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10418 14

certified_graph_case record008 24 34223943852096 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10419 14

certified_graph_case record009 24 34239548622864 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10420 14

certified_graph_case record010 24 34240604422144 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10421 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00167

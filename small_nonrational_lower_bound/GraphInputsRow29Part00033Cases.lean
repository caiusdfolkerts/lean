module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00033Checked
public import GraphInputsRow29Part00033Metadata
public import GraphInputsRow29Part00033Frames
public import GraphInputsRow29Part00033Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch108
public import GraphCoverageBatch144
public import GraphInputsRow29Part00033Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 7156835291392 GraphCoverageDescriptions.GraphCoverageBatch144.candidate14430 14

theorem record001_parameters : Parameters record001 (rowOfCode 29) 7156901351680 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 7156901351680 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10879 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 7156901351680
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch108.candidate10879_checked

theorem record001_result : Result (29, 7156901351680) :=
  of_direct_small 29 7156901351680 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00033.record001.direct_core, record001_parameters, record001_coverage⟩
#print axioms record001_result

certified_graph_case record002 29 7157062926336 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10880 14

certified_graph_case record003 29 7157065007104 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10881 14

certified_graph_case record004 29 7158246674448 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10882 14

certified_graph_case record005 29 7165421031680 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10883 14

certified_graph_case record006 29 7185770283264 GraphCoverageDescriptions.GraphCoverageBatch144.candidate14431 14

certified_graph_case record007 29 7185774510080 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10884 14

certified_graph_case record008 29 7185778086144 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10885 14

theorem record009_parameters : Parameters record009 (rowOfCode 29) 7186298177552 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 7186298177552 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10886 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 7186298177552
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.small_allowed record009 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch108.candidate10886_checked

theorem record009_result : Result (29, 7186298177552) :=
  of_direct_small 29 7186298177552 (by decide) ⟨record009, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00033.record009.direct_core, record009_parameters, record009_coverage⟩
#print axioms record009_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033

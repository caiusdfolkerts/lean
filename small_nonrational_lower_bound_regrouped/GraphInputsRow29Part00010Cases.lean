module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00010Checked
public import GraphInputsRow29Part00010Metadata
public import GraphInputsRow29Part00010Frames
public import GraphInputsRow29Part00010Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch106
public import GraphCoverageBatch143
public import GraphInputsRow29Part00010Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00010
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 2934146400256 GraphCoverageDescriptions.GraphCoverageBatch143.candidate14354 14

certified_graph_case record001 29 2942860034304 GraphCoverageDescriptions.GraphCoverageBatch143.candidate14355 14

certified_graph_case record002 29 2968439029760 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10648 14

certified_graph_case record003 29 2974948556800 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10649 14

certified_graph_case record004 29 2975072289024 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10650 14

certified_graph_case record005 29 3034803343616 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10651 14

certified_graph_case record006 29 3080298987648 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10652 14

certified_graph_case record007 29 3102382030848 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10653 14

certified_graph_case record008 29 3118952628352 GraphCoverageDescriptions.GraphCoverageBatch143.candidate14356 14

certified_graph_case record009 29 3135617695744 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10654 14

certified_graph_case record010 29 3140430659584 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10655 14

theorem record011_parameters : Parameters record011 (rowOfCode 29) 3140438982656 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record011_coverage : Coverage record011 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 3140438982656 :=
  GraphCoverageDescriptions.coverage_of_checked record011 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10656 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 3140438982656
    (by rfl) record011_cells_exact
    (GraphCoverageDescriptions.small_allowed record011 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch106.candidate10656_checked

theorem record011_result : Result (29, 3140438982656) :=
  of_direct_small 29 3140438982656 (by decide) ⟨record011, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00010.record011.direct_core, record011_parameters, record011_coverage⟩
#print axioms record011_result

certified_graph_case record012 29 3149020561408 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10657 14

certified_graph_case record013 29 3152644440320 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10658 14

certified_graph_case record014 29 3153313431552 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10659 14

certified_graph_case record015 29 3157073657856 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10660 14

theorem record016_parameters : Parameters record016 (rowOfCode 29) 3157610463232 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record016_coverage : Coverage record016 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 3157610463232 :=
  GraphCoverageDescriptions.coverage_of_checked record016 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10661 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 3157610463232
    (by rfl) record016_cells_exact
    (GraphCoverageDescriptions.small_allowed record016 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch106.candidate10661_checked

theorem record016_result : Result (29, 3157610463232) :=
  of_direct_small 29 3157610463232 (by decide) ⟨record016, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00010.record016.direct_core, record016_parameters, record016_coverage⟩
#print axioms record016_result

theorem record017_parameters : Parameters record017 (rowOfCode 29) 3164726165504 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record017_coverage : Coverage record017 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 3164726165504 :=
  GraphCoverageDescriptions.coverage_of_checked record017 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10662 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 3164726165504
    (by rfl) record017_cells_exact
    (GraphCoverageDescriptions.small_allowed record017 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch106.candidate10662_checked

theorem record017_result : Result (29, 3164726165504) :=
  of_direct_small 29 3164726165504 (by decide) ⟨record017, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00010.record017.direct_core, record017_parameters, record017_coverage⟩
#print axioms record017_result

certified_graph_case record018 29 3166806540288 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10663 14

certified_graph_case record019 29 3200042205184 GraphCoverageDescriptions.GraphCoverageBatch106.candidate10664 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00010

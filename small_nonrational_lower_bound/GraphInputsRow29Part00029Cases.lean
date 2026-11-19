module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00029Checked
public import GraphInputsRow29Part00029Metadata
public import GraphInputsRow29Part00029Frames
public import GraphInputsRow29Part00029Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch108
public import GraphCoverageBatch144
public import GraphInputsRow29Part00029Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00029
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 6844835693312 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10850 14

certified_graph_case record001 29 6851076817664 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10851 14

certified_graph_case record002 29 6854969426176 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10852 14

certified_graph_case record003 29 6854981715968 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10853 14

theorem record004_parameters : Parameters record004 (rowOfCode 29) 6855179896832 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 6855179896832 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10854 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 6855179896832
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch108.candidate10854_checked

theorem record004_result : Result (29, 6855179896832) :=
  of_direct_small 29 6855179896832 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00029.record004.direct_core, record004_parameters, record004_coverage⟩
#print axioms record004_result

certified_graph_case record005 29 6857598959616 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10855 14

certified_graph_case record006 29 6878731964672 GraphCoverageDescriptions.GraphCoverageBatch144.candidate14423 14

certified_graph_case record007 29 6909937647616 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10856 14

certified_graph_case record008 29 6912018022400 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10857 14

certified_graph_case record009 29 6977465942016 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10858 14

certified_graph_case record010 29 6982278905856 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10859 14

certified_graph_case record011 29 6982287228928 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10860 14

certified_graph_case record012 29 6983905247232 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10861 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00029

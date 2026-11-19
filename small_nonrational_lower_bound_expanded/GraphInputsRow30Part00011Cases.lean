module
prelude
public meta import GraphCases
public import GraphInputsRow30Part00011Checked
public import GraphInputsRow30Part00011Metadata
public import GraphInputsRow30Part00011Frames
public import GraphInputsRow30Part00011Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch108
public import GraphInputsRow30Part00011Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00011
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 30 6854969426176 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10852 14

certified_graph_case record001 30 6854981715968 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10853 14

certified_graph_case record002 30 6855179896832 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10854 14

certified_graph_case record003 30 6857598959616 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10855 14

certified_graph_case record004 30 6909937647616 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10856 14

theorem record005_parameters : Parameters record005 (rowOfCode 30) 6912018022400 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 6912018022400 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10857 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 6912018022400
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch108.candidate10857_checked

theorem record005_result : Result (30, 6912018022400) :=
  of_direct_small 30 6912018022400 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00011.record005.direct_core, record005_parameters, record005_coverage⟩

certified_graph_case record006 30 6977465942016 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10858 14

certified_graph_case record007 30 6982278905856 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10859 14

certified_graph_case record008 30 6982287228928 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10860 14

certified_graph_case record009 30 6983905247232 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10861 14

certified_graph_case record010 30 6986166960896 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10862 14

certified_graph_case record011 30 6986447978496 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10863 14

certified_graph_case record012 30 6988528353280 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10864 14

certified_graph_case record013 30 6999458709504 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10865 14

certified_graph_case record014 30 7003082653696 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10866 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00011

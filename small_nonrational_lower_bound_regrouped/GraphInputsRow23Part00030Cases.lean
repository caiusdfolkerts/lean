module
prelude
public meta import GraphCases
public import GraphInputsRow23Part00030Checked
public import GraphInputsRow23Part00030Metadata
public import GraphInputsRow23Part00030Frames
public import GraphInputsRow23Part00030Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch060
public import GraphInputsRow23Part00030Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 23 32782688452608 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06010 6

certified_graph_case record001 23 32783216934912 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06011 6

certified_graph_case record002 23 32788929576960 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06012 6

certified_graph_case record003 23 32789458059264 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06013 6

certified_graph_case record004 23 32804960346112 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06014 6

certified_graph_case record005 23 32804994809856 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06015 6

certified_graph_case record006 23 32806101057536 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06016 6

certified_graph_case record007 23 32813571178496 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06017 6

theorem record008_parameters : Parameters record008 (rowOfCode 23) 32822165241856 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32822165241856 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06018 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 32822165241856
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch060.candidate06018_checked

theorem record008_result : Result (23, 32822165241856) :=
  of_direct_small 23 32822165241856 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00030.record008.direct_core, record008_parameters, record008_coverage⟩
#print axioms record008_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00030

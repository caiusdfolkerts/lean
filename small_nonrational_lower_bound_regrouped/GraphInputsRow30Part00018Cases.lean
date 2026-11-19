module
prelude
public meta import GraphCases
public import GraphInputsRow30Part00018Checked
public import GraphInputsRow30Part00018Metadata
public import GraphInputsRow30Part00018Frames
public import GraphInputsRow30Part00018Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch110
public import GraphInputsRow30Part00018Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00018
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 30 10055202115616 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11060 14

certified_graph_case record001 30 10090165829632 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11061 14

certified_graph_case record002 30 10138830307328 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11062 14

certified_graph_case record003 30 10138941686016 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11063 14

certified_graph_case record004 30 10138953975808 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11064 14

certified_graph_case record005 30 10208472530944 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11065 14

certified_graph_case record006 30 10214713655296 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11066 14

certified_graph_case record007 30 10218410868737 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11067 14

certified_graph_case record008 30 10276000825344 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11068 14

certified_graph_case record009 30 10293696561152 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11069 14

certified_graph_case record010 30 10301617537024 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11070 14

certified_graph_case record011 30 10301890101248 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11071 14

certified_graph_case record012 30 10302154342400 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11072 14

certified_graph_case record013 30 10349399048192 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11073 14

certified_graph_case record014 30 10396574449664 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11074 14

certified_graph_case record015 30 10448894198016 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11075 14

certified_graph_case record016 30 10448894263296 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11076 14

certified_graph_case record017 30 10448996929792 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11077 14

certified_graph_case record018 30 10455599890432 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11078 14

theorem record019_parameters : Parameters record019 (rowOfCode 30) 10456781557776 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record019_coverage : Coverage record019 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10456781557776 :=
  GraphCoverageDescriptions.coverage_of_checked record019 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11079 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10456781557776
    (by rfl) record019_cells_exact
    (GraphCoverageDescriptions.small_allowed record019 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch110.candidate11079_checked

theorem record019_result : Result (30, 10456781557776) :=
  of_direct_small 30 10456781557776 (by decide) ⟨record019, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00018.record019.direct_core, record019_parameters, record019_coverage⟩
#print axioms record019_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00018

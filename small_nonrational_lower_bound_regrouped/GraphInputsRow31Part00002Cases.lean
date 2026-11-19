module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00002Checked
public import GraphInputsRow31Part00002Metadata
public import GraphInputsRow31Part00002Frames
public import GraphInputsRow31Part00002Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch155
public import GraphInputsRow31Part00002Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00002
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 31) 110067155072 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 110067155072 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15578 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 110067155072
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch155.candidate15578_checked

theorem record000_result : Result (31, 110067155072) :=
  of_direct_small 31 110067155072 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00002.record000.direct_core, record000_parameters, record000_coverage⟩
#print axioms record000_result

certified_graph_case record001 31 110339588352 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15579 14

certified_graph_case record002 31 114227741440 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15580 14

certified_graph_case record003 31 114231935232 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15581 14

certified_graph_case record004 31 114362105984 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15582 14

certified_graph_case record005 31 114500337920 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15583 14

certified_graph_case record006 31 114500403200 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15584 14

certified_graph_case record007 31 114634539264 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15585 14

certified_graph_case record008 31 123090272512 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15586 14

certified_graph_case record009 31 123090337792 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15587 14

certified_graph_case record010 31 129666916416 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15588 14

certified_graph_case record011 31 144461348992 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15589 14

certified_graph_case record012 31 182949314816 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15590 14

certified_graph_case record013 31 183217717504 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15591 14

certified_graph_case record014 31 183217782784 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15592 14

certified_graph_case record015 31 183219798272 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15593 14

certified_graph_case record016 31 185298092288 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15594 14

certified_graph_case record017 31 191539281920 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15595 14

certified_graph_case record018 31 191541297408 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15596 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00002

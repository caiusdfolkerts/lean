module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00124Checked
public import GraphInputsRow29Part00124Metadata
public import GraphInputsRow29Part00124Frames
public import GraphInputsRow29Part00124Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch116
public import GraphCoverageBatch149
public import GraphInputsRow29Part00124Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00124
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 21007368716288 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11635 14

certified_graph_case record001 29 21015946068608 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11636 14

certified_graph_case record002 29 21076077772800 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14988 14

certified_graph_case record003 29 21076086095872 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11637 14

certified_graph_case record004 29 21118423433472 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14989 14

certified_graph_case record005 29 21119160565760 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11638 14

certified_graph_case record006 29 21257072410624 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11639 14

certified_graph_case record007 29 21350955614208 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11640 14

theorem record008_parameters : Parameters record008 (rowOfCode 29) 21367598612480 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 21367598612480 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11641 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 21367598612480
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch116.candidate11641_checked

theorem record008_result : Result (29, 21367598612480) :=
  of_direct_small 29 21367598612480 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00124.record008.direct_core, record008_parameters, record008_coverage⟩
#print axioms record008_result

certified_graph_case record009 29 21374041096448 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11642 14

certified_graph_case record010 29 21378338193408 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11643 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00124

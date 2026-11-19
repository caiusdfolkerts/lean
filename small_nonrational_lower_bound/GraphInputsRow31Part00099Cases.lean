module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00099Checked
public import GraphInputsRow31Part00099Metadata
public import GraphInputsRow31Part00099Frames
public import GraphInputsRow31Part00099Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch164
public import GraphInputsRow31Part00099Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00099
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 21805549125632 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16458 14

certified_graph_case record001 31 21857227046912 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16459 14

theorem record002_parameters : Parameters record002 (rowOfCode 31) 21878699720704 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 21878699720704 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16460 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 21878699720704
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch164.candidate16460_checked

theorem record002_result : Result (31, 21878699720704) :=
  of_direct_small 31 21878699720704 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00099.record002.direct_core, record002_parameters, record002_coverage⟩
#print axioms record002_result

certified_graph_case record003 31 21926084870144 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16461 14

certified_graph_case record004 31 21934934851584 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16462 14

theorem record005_parameters : Parameters record005 (rowOfCode 31) 21947417100288 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 21947417100288 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16463 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 21947417100288
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch164.candidate16463_checked

theorem record005_result : Result (31, 21947417100288) :=
  of_direct_small 31 21947417100288 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00099.record005.direct_core, record005_parameters, record005_coverage⟩
#print axioms record005_result

certified_graph_case record006 31 21993567043840 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16464 14

certified_graph_case record007 31 21993765224704 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16465 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00099

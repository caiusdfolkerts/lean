module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00115Checked
public import GraphInputsRow31Part00115Metadata
public import GraphInputsRow31Part00115Frames
public import GraphInputsRow31Part00115Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch165
public import GraphInputsRow31Part00115Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00115
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 26126328004608 GraphCoverageDescriptions.GraphCoverageBatch165.candidate16575 14

certified_graph_case record001 31 26132057423872 GraphCoverageDescriptions.GraphCoverageBatch165.candidate16576 14

certified_graph_case record002 31 26139206615040 GraphCoverageDescriptions.GraphCoverageBatch165.candidate16577 14

certified_graph_case record003 31 26207890571264 GraphCoverageDescriptions.GraphCoverageBatch165.candidate16578 14

certified_graph_case record004 31 26250859053056 GraphCoverageDescriptions.GraphCoverageBatch165.candidate16579 14

certified_graph_case record005 31 26319584755712 GraphCoverageDescriptions.GraphCoverageBatch165.candidate16580 14

certified_graph_case record006 31 26336756236288 GraphCoverageDescriptions.GraphCoverageBatch165.candidate16581 14

theorem record007_parameters : Parameters record007 (rowOfCode 31) 26391807541504 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 26391807541504 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch165.candidate16582 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 26391807541504
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch165.candidate16582_checked

theorem record007_result : Result (31, 26391807541504) :=
  of_direct_small 31 26391807541504 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00115.record007.direct_core, record007_parameters, record007_coverage⟩

certified_graph_case record008 31 26392080171136 GraphCoverageDescriptions.GraphCoverageBatch165.candidate16583 14

certified_graph_case record009 31 26428349415424 GraphCoverageDescriptions.GraphCoverageBatch165.candidate16584 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00115

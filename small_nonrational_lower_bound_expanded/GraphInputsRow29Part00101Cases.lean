module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00101Checked
public import GraphInputsRow29Part00101Metadata
public import GraphInputsRow29Part00101Frames
public import GraphInputsRow29Part00101Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch115
public import GraphCoverageBatch147
public import GraphInputsRow29Part00101Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00101
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 17235980582912 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11510 14

certified_graph_case record001 29 17236509065216 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11511 14

certified_graph_case record002 29 17248609698048 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14780 14

certified_graph_case record003 29 17274358661120 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14781 14

certified_graph_case record004 29 17292083593216 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11512 14

certified_graph_case record005 29 17309255073792 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11513 14

theorem record006_parameters : Parameters record006 (rowOfCode 29) 17317602004992 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 17317602004992 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11514 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 17317602004992
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch115.candidate11514_checked

theorem record006_result : Result (29, 17317602004992) :=
  of_direct_small 29 17317602004992 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00101.record006.direct_core, record006_parameters, record006_coverage⟩

certified_graph_case record007 29 17326183874560 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14782 14

certified_graph_case record008 29 17326451720720 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11515 14

theorem record009_parameters : Parameters record009 (rowOfCode 29) 17457033052160 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 17457033052160 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11516 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 17457033052160
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.small_allowed record009 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch115.candidate11516_checked

theorem record009_result : Result (29, 17457033052160) :=
  of_direct_small 29 17457033052160 (by decide) ⟨record009, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00101.record009.direct_core, record009_parameters, record009_coverage⟩

certified_graph_case record010 29 17480516895236 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11517 14

theorem record011_parameters : Parameters record011 (rowOfCode 29) 17493678620672 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record011_coverage : Coverage record011 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 17493678620672 :=
  GraphCoverageDescriptions.coverage_of_checked record011 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11518 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 17493678620672
    (by rfl) record011_cells_exact
    (GraphCoverageDescriptions.small_allowed record011 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch115.candidate11518_checked

theorem record011_result : Result (29, 17493678620672) :=
  of_direct_small 29 17493678620672 (by decide) ⟨record011, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00101.record011.direct_core, record011_parameters, record011_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00101

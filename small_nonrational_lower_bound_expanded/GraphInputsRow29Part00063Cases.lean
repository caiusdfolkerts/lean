module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00063Checked
public import GraphInputsRow29Part00063Metadata
public import GraphInputsRow29Part00063Frames
public import GraphInputsRow29Part00063Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch111
public import GraphCoverageBatch145
public import GraphInputsRow29Part00063Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00063
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 11961085493248 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11154 14

theorem record001_parameters : Parameters record001 (rowOfCode 29) 11961217613824 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 11961217613824 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11155 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 11961217613824
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch111.candidate11155_checked

theorem record001_result : Result (29, 11961217613824) :=
  of_direct_small 29 11961217613824 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00063.record001.direct_core, record001_parameters, record001_coverage⟩

certified_graph_case record002 29 11963937652736 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11156 14

certified_graph_case record003 29 11963945975808 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11157 14

certified_graph_case record004 29 11966921867520 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11158 14

theorem record005_parameters : Parameters record005 (rowOfCode 29) 11967198658560 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 11967198658560 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11159 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 11967198658560
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch111.candidate11159_checked

theorem record005_result : Result (29, 11967198658560) :=
  of_direct_small 29 11967198658560 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00063.record005.direct_core, record005_parameters, record005_coverage⟩

certified_graph_case record006 29 11967458738176 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11160 14

certified_graph_case record007 29 11975511801984 GraphCoverageDescriptions.GraphCoverageBatch145.candidate14586 14

certified_graph_case record008 29 11982993375360 GraphCoverageDescriptions.GraphCoverageBatch145.candidate14587 14

theorem record009_parameters : Parameters record009 (rowOfCode 29) 11984101736448 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 11984101736448 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11161 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 11984101736448
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.small_allowed record009 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch111.candidate11161_checked

theorem record009_result : Result (29, 11984101736448) :=
  of_direct_small 29 11984101736448 (by decide) ⟨record009, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00063.record009.direct_core, record009_parameters, record009_coverage⟩

certified_graph_case record010 29 11984238018560 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11162 14

certified_graph_case record011 29 11995864662272 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11163 14

certified_graph_case record012 29 11996133130240 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11164 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00063

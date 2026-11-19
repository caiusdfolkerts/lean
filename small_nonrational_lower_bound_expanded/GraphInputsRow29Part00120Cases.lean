module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00120Checked
public import GraphInputsRow29Part00120Metadata
public import GraphInputsRow29Part00120Frames
public import GraphInputsRow29Part00120Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch116
public import GraphCoverageBatch149
public import GraphInputsRow29Part00120Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00120
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 20690539413504 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14971 14

certified_graph_case record001 29 20694295412992 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14972 14

certified_graph_case record002 29 20694572204032 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11608 14

certified_graph_case record003 29 20694638264320 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11609 14

certified_graph_case record004 29 20694832283648 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14973 14

certified_graph_case record005 29 20702885347456 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14974 14

theorem record006_parameters : Parameters record006 (rowOfCode 29) 20710366920832 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 20710366920832 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11610 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 20710366920832
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch116.candidate11610_checked

theorem record006_result : Result (29, 20710366920832) :=
  of_direct_small 29 20710366920832 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00120.record006.direct_core, record006_parameters, record006_coverage⟩

certified_graph_case record007 29 20711611564032 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11611 14

certified_graph_case record008 29 20723238207744 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14975 14

certified_graph_case record009 29 20723506675712 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14976 14

theorem record010_parameters : Parameters record010 (rowOfCode 29) 20723514998784 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record010_coverage : Coverage record010 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 20723514998784 :=
  GraphCoverageDescriptions.coverage_of_checked record010 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11612 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 20723514998784
    (by rfl) record010_cells_exact
    (GraphCoverageDescriptions.small_allowed record010 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch116.candidate11612_checked

theorem record010_result : Result (29, 20723514998784) :=
  of_direct_small 29 20723514998784 (by decide) ⟨record010, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00120.record010.direct_core, record010_parameters, record010_coverage⟩

theorem record011_parameters : Parameters record011 (rowOfCode 29) 20723775078400 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record011_coverage : Coverage record011 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 20723775078400 :=
  GraphCoverageDescriptions.coverage_of_checked record011 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14977 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 20723775078400
    (by rfl) record011_cells_exact
    (GraphCoverageDescriptions.small_allowed record011 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch149.candidate14977_checked

theorem record011_result : Result (29, 20723775078400) :=
  of_direct_small 29 20723775078400 (by decide) ⟨record011, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00120.record011.direct_core, record011_parameters, record011_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00120

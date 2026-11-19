module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00119Checked
public import GraphInputsRow29Part00119Metadata
public import GraphInputsRow29Part00119Frames
public import GraphInputsRow29Part00119Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch116
public import GraphCoverageBatch149
public import GraphInputsRow29Part00119Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00119
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 29) 20526456176640 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 20526456176640 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14963 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 20526456176640
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch149.candidate14963_checked

theorem record000_result : Result (29, 20526456176640) :=
  of_direct_small 29 20526456176640 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00119.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 29 20567121986176 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14964 14

certified_graph_case record002 29 20622688682240 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14965 14

certified_graph_case record003 29 20622957117568 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14966 14

certified_graph_case record004 29 20634300088448 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14967 14

certified_graph_case record005 29 20634304282624 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14968 14

certified_graph_case record006 29 20687922168064 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14969 14

theorem record007_parameters : Parameters record007 (rowOfCode 29) 20688190636032 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 20688190636032 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11603 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 20688190636032
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch116.candidate11603_checked

theorem record007_result : Result (29, 20688190636032) :=
  of_direct_small 29 20688190636032 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00119.record007.direct_core, record007_parameters, record007_coverage⟩

certified_graph_case record008 29 20688198959104 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11604 14

certified_graph_case record009 29 20688459038720 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11605 14

theorem record010_parameters : Parameters record010 (rowOfCode 29) 20688591159296 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record010_coverage : Coverage record010 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 20688591159296 :=
  GraphCoverageDescriptions.coverage_of_checked record010 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11606 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 20688591159296
    (by rfl) record010_cells_exact
    (GraphCoverageDescriptions.small_allowed record010 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch116.candidate11606_checked

theorem record010_result : Result (29, 20688591159296) :=
  of_direct_small 29 20688591159296 (by decide) ⟨record010, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00119.record010.direct_core, record010_parameters, record010_coverage⟩

certified_graph_case record011 29 20690271010816 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14970 14

certified_graph_case record012 29 20690279333888 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11607 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00119

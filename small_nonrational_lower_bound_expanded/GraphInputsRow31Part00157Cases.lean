module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00157Checked
public import GraphInputsRow31Part00157Metadata
public import GraphInputsRow31Part00157Frames
public import GraphInputsRow31Part00157Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch167
public import GraphCoverageBatch168
public import GraphInputsRow31Part00157Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00157
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 31) 31068451774464 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31068451774464 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16795 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 31068451774464
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch167.candidate16795_checked

theorem record000_result : Result (31, 31068451774464) :=
  of_direct_small 31 31068451774464 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00157.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 31 31074122998016 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16796 14

theorem record002_parameters : Parameters record002 (rowOfCode 31) 31079525269632 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31079525269632 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16797 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 31079525269632
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch167.candidate16797_checked

theorem record002_result : Result (31, 31079525269632) :=
  of_direct_small 31 31079525269632 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00157.record002.direct_core, record002_parameters, record002_coverage⟩

certified_graph_case record003 31 31079860805632 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16798 14

certified_graph_case record004 31 31080565457024 GraphCoverageDescriptions.GraphCoverageBatch167.candidate16799 14

theorem record005_parameters : Parameters record005 (rowOfCode 31) 31080934023168 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31080934023168 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch168.candidate16800 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 31080934023168
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch168.candidate16800_checked

theorem record005_result : Result (31, 31080934023168) :=
  of_direct_small 31 31080934023168 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00157.record005.direct_core, record005_parameters, record005_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00157

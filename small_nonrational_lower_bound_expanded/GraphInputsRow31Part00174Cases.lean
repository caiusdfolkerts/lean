module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00174Checked
public import GraphInputsRow31Part00174Metadata
public import GraphInputsRow31Part00174Frames
public import GraphInputsRow31Part00174Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch169
public import GraphInputsRow31Part00174Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00174
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 34635690149904 GraphCoverageDescriptions.GraphCoverageBatch169.candidate16910 14

certified_graph_case record001 31 34635707383808 GraphCoverageDescriptions.GraphCoverageBatch169.candidate16911 14

theorem record002_parameters : Parameters record002 (rowOfCode 31) 34635727831040 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34635727831040 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch169.candidate16912 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 34635727831040
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch169.candidate16912_checked

theorem record002_result : Result (31, 34635727831040) :=
  of_direct_small 31 34635727831040 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00174.record002.direct_core, record002_parameters, record002_coverage⟩

certified_graph_case record003 31 34635740348928 GraphCoverageDescriptions.GraphCoverageBatch169.candidate16913 14

certified_graph_case record004 31 34635748737024 GraphCoverageDescriptions.GraphCoverageBatch169.candidate16914 14

certified_graph_case record005 31 34635828494336 GraphCoverageDescriptions.GraphCoverageBatch169.candidate16915 14

theorem record006_parameters : Parameters record006 (rowOfCode 31) 34636244189184 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34636244189184 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch169.candidate16916 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 34636244189184
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch169.candidate16916_checked

theorem record006_result : Result (31, 34636244189184) :=
  of_direct_small 31 34636244189184 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00174.record006.direct_core, record006_parameters, record006_coverage⟩

theorem record007_parameters : Parameters record007 (rowOfCode 31) 34644321894400 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34644321894400 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch169.candidate16917 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 34644321894400
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch169.candidate16917_checked

theorem record007_result : Result (31, 34644321894400) :=
  of_direct_small 31 34644321894400 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00174.record007.direct_core, record007_parameters, record007_coverage⟩

certified_graph_case record008 31 34644850376704 GraphCoverageDescriptions.GraphCoverageBatch169.candidate16918 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00174

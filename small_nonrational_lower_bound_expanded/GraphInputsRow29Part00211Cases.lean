module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00211Checked
public import GraphInputsRow29Part00211Metadata
public import GraphInputsRow29Part00211Frames
public import GraphInputsRow29Part00211Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch120
public import GraphCoverageBatch154
public import GraphInputsRow29Part00211Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00211
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 29) 29277198762112 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29277198762112 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 29277198762112
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch120.candidate12000_checked

theorem record000_result : Result (29, 29277198762112) :=
  of_direct_small 29 29277198762112 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00211.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 29 29277204516864 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12001 14

certified_graph_case record002 29 29281744847376 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12002 14

certified_graph_case record003 29 29283288617216 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12003 14

theorem record004_parameters : Parameters record004 (rowOfCode 29) 29283643822080 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29283643822080 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 29283643822080
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch120.candidate12004_checked

theorem record004_result : Result (29, 29283643822080) :=
  of_direct_small 29 29283643822080 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00211.record004.direct_core, record004_parameters, record004_coverage⟩

certified_graph_case record005 29 29284362093312 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15427 14

certified_graph_case record006 29 29284498472960 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15428 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00211

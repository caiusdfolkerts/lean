module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00141Checked
public import GraphInputsRow29Part00141Metadata
public import GraphInputsRow29Part00141Frames
public import GraphInputsRow29Part00141Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch117
public import GraphCoverageBatch151
public import GraphInputsRow29Part00141Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00141
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 24103375405056 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11730 14

certified_graph_case record001 29 24103912210432 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11731 14

certified_graph_case record002 29 24104027815936 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11732 14

certified_graph_case record003 29 24107651629056 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15149 14

theorem record004_parameters : Parameters record004 (rowOfCode 29) 24192647987456 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24192647987456 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11733 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24192647987456
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch117.candidate11733_checked

theorem record004_result : Result (29, 24192647987456) :=
  of_direct_small 29 24192647987456 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00141.record004.direct_core, record004_parameters, record004_coverage⟩

certified_graph_case record005 29 24195205439616 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15150 14

theorem record006_parameters : Parameters record006 (rowOfCode 29) 24199502504000 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24199502504000 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11734 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24199502504000
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch117.candidate11734_checked

theorem record006_result : Result (29, 24199502504000) :=
  of_direct_small 29 24199502504000 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00141.record006.direct_core, record006_parameters, record006_coverage⟩

certified_graph_case record007 29 24225916682496 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11735 14

certified_graph_case record008 29 24229598756864 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15151 14

certified_graph_case record009 29 24230729646336 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15152 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00141

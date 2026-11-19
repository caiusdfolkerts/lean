module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00075Checked
public import GraphInputsRow29Part00075Metadata
public import GraphInputsRow29Part00075Frames
public import GraphInputsRow29Part00075Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch112
public import GraphCoverageBatch146
public import GraphInputsRow29Part00075Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00075
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 29) 12578483109888 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 12578483109888 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch112.candidate11223 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 12578483109888
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch112.candidate11223_checked

theorem record000_result : Result (29, 12578483109888) :=
  of_direct_small 29 12578483109888 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00075.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 29 12582106857728 GraphCoverageDescriptions.GraphCoverageBatch146.candidate14628 14

certified_graph_case record002 29 12582912000512 GraphCoverageDescriptions.GraphCoverageBatch146.candidate14629 14

certified_graph_case record003 29 12584455831552 GraphCoverageDescriptions.GraphCoverageBatch146.candidate14630 14

theorem record004_parameters : Parameters record004 (rowOfCode 29) 12584810971136 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 12584810971136 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch112.candidate11224 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 12584810971136
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch112.candidate11224_checked

theorem record004_result : Result (29, 12584810971136) :=
  of_direct_small 29 12584810971136 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00075.record004.direct_core, record004_parameters, record004_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00075

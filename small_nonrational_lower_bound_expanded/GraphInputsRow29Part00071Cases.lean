module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00071Checked
public import GraphInputsRow29Part00071Metadata
public import GraphInputsRow29Part00071Frames
public import GraphInputsRow29Part00071Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch112
public import GraphCoverageBatch146
public import GraphInputsRow29Part00071Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00071
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 12388163141760 GraphCoverageDescriptions.GraphCoverageBatch146.candidate14624 14

theorem record001_parameters : Parameters record001 (rowOfCode 29) 12447958204672 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 12447958204672 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch112.candidate11210 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 12447958204672
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch112.candidate11210_checked

theorem record001_result : Result (29, 12447958204672) :=
  of_direct_small 29 12447958204672 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00071.record001.direct_core, record001_parameters, record001_coverage⟩

certified_graph_case record002 29 12448495075328 GraphCoverageDescriptions.GraphCoverageBatch112.candidate11211 14

certified_graph_case record003 29 12456548139136 GraphCoverageDescriptions.GraphCoverageBatch146.candidate14625 14

certified_graph_case record004 29 12465138073600 GraphCoverageDescriptions.GraphCoverageBatch112.candidate11212 14

theorem record005_parameters : Parameters record005 (rowOfCode 29) 12465274355712 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 12465274355712 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch112.candidate11213 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 12465274355712
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch112.candidate11213_checked

theorem record005_result : Result (29, 12465274355712) :=
  of_direct_small 29 12465274355712 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00071.record005.direct_core, record005_parameters, record005_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00071

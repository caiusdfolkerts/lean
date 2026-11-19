module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00079Checked
public import GraphInputsRow24Part00079Metadata
public import GraphInputsRow24Part00079Frames
public import GraphInputsRow24Part00079Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch089
public import GraphInputsRow24Part00079Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00079
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 24423434354688 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08950 14

theorem record001_parameters : Parameters record001 (rowOfCode 24) 24423442677760 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24423442677760 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08951 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24423442677760
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch089.candidate08951_checked

theorem record001_result : Result (24, 24423442677760) :=
  of_direct_small 24 24423442677760 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00079.record001.direct_core, record001_parameters, record001_coverage⟩

certified_graph_case record002 24 24432076718336 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08952 14

certified_graph_case record003 24 24432085106688 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08953 14

certified_graph_case record004 24 24432208838912 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08954 14

theorem record005_parameters : Parameters record005 (rowOfCode 24) 24432217227264 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24432217227264 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08955 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24432217227264
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch089.candidate08955_checked

theorem record005_result : Result (24, 24432217227264) :=
  of_direct_small 24 24432217227264 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00079.record005.direct_core, record005_parameters, record005_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00079

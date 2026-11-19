module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00033Checked
public import GraphInputsRow24Part00033Metadata
public import GraphInputsRow24Part00033Frames
public import GraphInputsRow24Part00033Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch076
public import GraphInputsRow24Part00033Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 16748770230272 GraphCoverageDescriptions.GraphCoverageBatch076.candidate07625 14

certified_graph_case record001 24 16752658415616 GraphCoverageDescriptions.GraphCoverageBatch076.candidate07626 14

certified_graph_case record002 24 16757091729408 GraphCoverageDescriptions.GraphCoverageBatch076.candidate07627 14

certified_graph_case record003 24 16757620211712 GraphCoverageDescriptions.GraphCoverageBatch076.candidate07628 14

certified_graph_case record004 24 16767638667280 GraphCoverageDescriptions.GraphCoverageBatch076.candidate07629 14

certified_graph_case record005 24 16767846211600 GraphCoverageDescriptions.GraphCoverageBatch076.candidate07630 14

certified_graph_case record006 24 16769838417936 GraphCoverageDescriptions.GraphCoverageBatch076.candidate07631 14

theorem record007_parameters : Parameters record007 (rowOfCode 24) 16776211662864 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 16776211662864 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch076.candidate07632 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 16776211662864
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch076.candidate07632_checked

theorem record007_result : Result (24, 16776211662864) :=
  of_direct_small 24 16776211662864 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00033.record007.direct_core, record007_parameters, record007_coverage⟩
#print axioms record007_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00033

module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00133Checked
public import GraphInputsRow24Part00133Metadata
public import GraphInputsRow24Part00133Frames
public import GraphInputsRow24Part00133Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch100
public import GraphInputsRow24Part00133Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 31546267467776 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10035 14

certified_graph_case record001 24 31551971721472 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10036 14

certified_graph_case record002 24 31552508592128 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10037 14

certified_graph_case record003 24 31552516915200 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10038 14

certified_graph_case record004 24 31553011908864 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10039 14

certified_graph_case record005 24 31560561623296 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10040 14

certified_graph_case record006 24 31560830091264 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10041 14

certified_graph_case record007 24 31560838414336 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10042 14

certified_graph_case record008 24 31561299795968 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10043 14

certified_graph_case record009 24 31561601810688 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10044 14

certified_graph_case record010 24 31562373013504 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10045 14

certified_graph_case record011 24 31568044237056 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10046 14

theorem record012_parameters : Parameters record012 (rowOfCode 24) 31569151590400 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record012_coverage : Coverage record012 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31569151590400 :=
  GraphCoverageDescriptions.coverage_of_checked record012 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10047 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 31569151590400
    (by rfl) record012_cells_exact
    (GraphCoverageDescriptions.small_allowed record012 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch100.candidate10047_checked

theorem record012_result : Result (24, 31569151590400) :=
  of_direct_small 24 31569151590400 (by decide) ⟨record012, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00133.record012.direct_core, record012_parameters, record012_coverage⟩
#print axioms record012_result

theorem record013_parameters : Parameters record013 (rowOfCode 24) 31569688395776 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record013_coverage : Coverage record013 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31569688395776 :=
  GraphCoverageDescriptions.coverage_of_checked record013 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10048 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 31569688395776
    (by rfl) record013_cells_exact
    (GraphCoverageDescriptions.small_allowed record013 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch100.candidate10048_checked

theorem record013_result : Result (24, 31569688395776) :=
  of_direct_small 24 31569688395776 (by decide) ⟨record013, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00133.record013.direct_core, record013_parameters, record013_coverage⟩
#print axioms record013_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00133

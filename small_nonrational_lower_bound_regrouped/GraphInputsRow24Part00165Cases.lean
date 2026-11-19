module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00165Checked
public import GraphInputsRow24Part00165Metadata
public import GraphInputsRow24Part00165Frames
public import GraphInputsRow24Part00165Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch103
public import GraphInputsRow24Part00165Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 33742623145984 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10379 14

certified_graph_case record001 24 33742631469056 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10380 14

certified_graph_case record002 24 33742672691200 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10381 14

certified_graph_case record003 24 33750423707648 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10382 14

theorem record004_parameters : Parameters record004 (rowOfCode 24) 33750926893312 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 33750926893312 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10383 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 33750926893312
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch103.candidate10383_checked

theorem record004_result : Result (24, 33750926893312) :=
  of_direct_small 24 33750926893312 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00165.record004.direct_core, record004_parameters, record004_coverage⟩
#print axioms record004_result

theorem record005_parameters : Parameters record005 (rowOfCode 24) 33751530734080 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 33751530734080 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10384 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 33751530734080
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch103.candidate10384_checked

theorem record005_result : Result (24, 33751530734080) :=
  of_direct_small 24 33751530734080 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00165.record005.direct_core, record005_parameters, record005_coverage⟩
#print axioms record005_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00165

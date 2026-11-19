module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00171Checked
public import GraphInputsRow24Part00171Metadata
public import GraphInputsRow24Part00171Frames
public import GraphInputsRow24Part00171Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch104
public import GraphInputsRow24Part00171Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 24) 34675150029312 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34675150029312 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10451 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 34675150029312
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch104.candidate10451_checked

theorem record000_result : Result (24, 34675150029312) :=
  of_direct_small 24 34675150029312 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00171.record000.direct_core, record000_parameters, record000_coverage⟩
#print axioms record000_result

theorem record001_parameters : Parameters record001 (rowOfCode 24) 34675150553088 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34675150553088 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10452 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 34675150553088
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch104.candidate10452_checked

theorem record001_result : Result (24, 34675150553088) :=
  of_direct_small 24 34675150553088 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00171.record001.direct_core, record001_parameters, record001_coverage⟩
#print axioms record001_result

theorem record002_parameters : Parameters record002 (rowOfCode 24) 34681861050624 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34681861050624 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10453 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 34681861050624
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch104.candidate10453_checked

theorem record002_result : Result (24, 34681861050624) :=
  of_direct_small 24 34681861050624 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00171.record002.direct_core, record002_parameters, record002_coverage⟩
#print axioms record002_result

certified_graph_case record003 24 34681895059456 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10454 14

certified_graph_case record004 24 34682976600064 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10455 14

certified_graph_case record005 24 34683505082368 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10456 14

certified_graph_case record006 24 34699074863104 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10457 14

theorem record007_parameters : Parameters record007 (rowOfCode 24) 34703629619200 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34703629619200 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10458 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 34703629619200
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch104.candidate10458_checked

theorem record007_result : Result (24, 34703629619200) :=
  of_direct_small 24 34703629619200 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00171.record007.direct_core, record007_parameters, record007_coverage⟩
#print axioms record007_result

certified_graph_case record008 24 34712462690320 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10459 14

certified_graph_case record009 24 34712479334928 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10460 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171

module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00126Checked
public import GraphInputsRow24Part00126Metadata
public import GraphInputsRow24Part00126Frames
public import GraphInputsRow24Part00126Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch099
public import GraphInputsRow24Part00126Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00126
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 31050537435136 GraphCoverageDescriptions.GraphCoverageBatch099.candidate09912 14

theorem record001_parameters : Parameters record001 (rowOfCode 24) 31050809999360 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31050809999360 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch099.candidate09913 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 31050809999360
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch099.candidate09913_checked

theorem record001_result : Result (24, 31050809999360) :=
  of_direct_small 24 31050809999360 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00126.record001.direct_core, record001_parameters, record001_coverage⟩

theorem record002_parameters : Parameters record002 (rowOfCode 24) 31051272421376 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31051272421376 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch099.candidate09914 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 31051272421376
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch099.candidate09914_checked

theorem record002_result : Result (24, 31051272421376) :=
  of_direct_small 24 31051272421376 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00126.record002.direct_core, record002_parameters, record002_coverage⟩

theorem record003_parameters : Parameters record003 (rowOfCode 24) 31057513545728 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31057513545728 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch099.candidate09915 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 31057513545728
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch099.candidate09915_checked

theorem record003_result : Result (24, 31057513545728) :=
  of_direct_small 24 31057513545728 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00126.record003.direct_core, record003_parameters, record003_coverage⟩

certified_graph_case record004 24 31064534827136 GraphCoverageDescriptions.GraphCoverageBatch099.candidate09916 14

certified_graph_case record005 24 31096730304640 GraphCoverageDescriptions.GraphCoverageBatch099.candidate09917 14

certified_graph_case record006 24 31175423885312 GraphCoverageDescriptions.GraphCoverageBatch099.candidate09918 14

certified_graph_case record007 24 31202208661504 GraphCoverageDescriptions.GraphCoverageBatch099.candidate09919 14

certified_graph_case record008 24 31235246145536 GraphCoverageDescriptions.GraphCoverageBatch099.candidate09920 14

certified_graph_case record009 24 31235444326400 GraphCoverageDescriptions.GraphCoverageBatch099.candidate09921 14

certified_graph_case record010 24 31235485483264 GraphCoverageDescriptions.GraphCoverageBatch099.candidate09922 14

certified_graph_case record011 24 31239650213888 GraphCoverageDescriptions.GraphCoverageBatch099.candidate09923 14

certified_graph_case record012 24 31244343575104 GraphCoverageDescriptions.GraphCoverageBatch099.candidate09924 14

certified_graph_case record013 24 31260986720256 GraphCoverageDescriptions.GraphCoverageBatch099.candidate09925 14

certified_graph_case record014 24 31274149347328 GraphCoverageDescriptions.GraphCoverageBatch099.candidate09926 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00126

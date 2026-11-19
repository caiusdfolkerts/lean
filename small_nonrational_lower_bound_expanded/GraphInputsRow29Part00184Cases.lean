module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00184Checked
public import GraphInputsRow29Part00184Metadata
public import GraphInputsRow29Part00184Frames
public import GraphInputsRow29Part00184Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch119
public import GraphCoverageBatch153
public import GraphInputsRow29Part00184Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 26991254339712 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15333 14

certified_graph_case record001 29 26992527818880 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15334 14

certified_graph_case record002 29 27015638491136 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15335 14

certified_graph_case record003 29 27015906861184 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15336 14

certified_graph_case record004 29 27015910527008 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11908 14

theorem record005_parameters : Parameters record005 (rowOfCode 29) 27016757838080 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 27016757838080 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15337 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 27016757838080
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch153.candidate15337_checked

theorem record005_result : Result (29, 27016757838080) :=
  of_direct_small 29 27016757838080 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00184.record005.direct_core, record005_parameters, record005_coverage⟩

theorem record006_parameters : Parameters record006 (rowOfCode 29) 27016762032640 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 27016762032640 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11909 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 27016762032640
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch119.candidate11909_checked

theorem record006_result : Result (29, 27016762032640) :=
  of_direct_small 29 27016762032640 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00184.record006.direct_core, record006_parameters, record006_coverage⟩

theorem record007_parameters : Parameters record007 (rowOfCode 29) 27016766226432 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 27016766226432 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11910 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 27016766226432
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch119.candidate11910_checked

theorem record007_result : Result (29, 27016766226432) :=
  of_direct_small 29 27016766226432 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00184.record007.direct_core, record007_parameters, record007_coverage⟩

certified_graph_case record008 29 27016963432576 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15338 14

certified_graph_case record009 29 27017034596353 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15339 14

certified_graph_case record010 29 27080062935296 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15340 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00184

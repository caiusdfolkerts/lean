module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00105Checked
public import GraphInputsRow24Part00105Metadata
public import GraphInputsRow24Part00105Frames
public import GraphInputsRow24Part00105Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch094
public import GraphInputsRow24Part00105Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00105
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 25963115118592 GraphCoverageDescriptions.GraphCoverageBatch094.candidate09401 14

theorem record001_parameters : Parameters record001 (rowOfCode 24) 25964427870208 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25964427870208 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch094.candidate09402 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25964427870208
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch094.candidate09402_checked

theorem record001_result : Result (24, 25964427870208) :=
  of_direct_small 24 25964427870208 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00105.record001.direct_core, record001_parameters, record001_coverage⟩

theorem record002_parameters : Parameters record002 (rowOfCode 24) 25964956352512 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25964956352512 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch094.candidate09403 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25964956352512
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch094.candidate09403_checked

theorem record002_result : Result (24, 25964956352512) :=
  of_direct_small 24 25964956352512 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00105.record002.direct_core, record002_parameters, record002_coverage⟩

theorem record003_parameters : Parameters record003 (rowOfCode 24) 25976121856256 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25976121856256 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch094.candidate09404 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25976121856256
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch094.candidate09404_checked

theorem record003_result : Result (24, 25976121856256) :=
  of_direct_small 24 25976121856256 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00105.record003.direct_core, record003_parameters, record003_coverage⟩

certified_graph_case record004 24 25976524509248 GraphCoverageDescriptions.GraphCoverageBatch094.candidate09405 14

theorem record005_parameters : Parameters record005 (rowOfCode 24) 25993284814864 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25993284814864 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch094.candidate09406 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25993284814864
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch094.candidate09406_checked

theorem record005_result : Result (24, 25993284814864) :=
  of_direct_small 24 25993284814864 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00105.record005.direct_core, record005_parameters, record005_coverage⟩

certified_graph_case record006 24 26113556615424 GraphCoverageDescriptions.GraphCoverageBatch094.candidate09407 14

certified_graph_case record007 24 26113695027264 GraphCoverageDescriptions.GraphCoverageBatch094.candidate09408 14

certified_graph_case record008 24 26130719574032 GraphCoverageDescriptions.GraphCoverageBatch094.candidate09409 14

certified_graph_case record009 24 26188600901632 GraphCoverageDescriptions.GraphCoverageBatch094.candidate09410 14

certified_graph_case record010 24 26220796379136 GraphCoverageDescriptions.GraphCoverageBatch094.candidate09411 14

certified_graph_case record011 24 26319584888832 GraphCoverageDescriptions.GraphCoverageBatch094.candidate09412 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00105

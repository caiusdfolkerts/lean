module
prelude
public meta import GraphCases
public import GraphInputsRow30Part00050Checked
public import GraphInputsRow30Part00050Metadata
public import GraphInputsRow30Part00050Frames
public import GraphInputsRow30Part00050Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch120
public import GraphCoverageBatch155
public import GraphInputsRow30Part00050Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00050
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 30 30516027851280 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12065 14

certified_graph_case record001 30 30717606234120 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12066 14

certified_graph_case record002 30 30717623011328 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12067 14

theorem record003_parameters : Parameters record003 (rowOfCode 30) 30717623271424 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 30717623271424 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12068 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 30717623271424
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch120.candidate12068_checked

theorem record003_result : Result (30, 30717623271424) :=
  of_direct_small 30 30717623271424 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00050.record003.direct_core, record003_parameters, record003_coverage⟩
#print axioms record003_result

certified_graph_case record004 30 30787452838144 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15561 14

certified_graph_case record005 30 30787452895264 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15562 14

certified_graph_case record006 30 30787485868288 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12069 14

theorem record007_parameters : Parameters record007 (rowOfCode 30) 30787485925408 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 30787485925408 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15563 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 30787485925408
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch155.candidate15563_checked

theorem record007_result : Result (30, 30787485925408) :=
  of_direct_small 30 30787485925408 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00050.record007.direct_core, record007_parameters, record007_coverage⟩
#print axioms record007_result

certified_graph_case record008 30 30787555106848 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12070 14

certified_graph_case record009 30 30788628844576 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12071 14

certified_graph_case record010 30 30789649597184 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12072 14

certified_graph_case record011 30 30789658050560 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12073 14

certified_graph_case record012 30 30789685415968 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12074 14

certified_graph_case record013 30 30789724110848 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12075 14

certified_graph_case record014 30 30790126682240 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12076 14

certified_graph_case record015 30 30790126714880 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12077 14

certified_graph_case record016 30 30790230478880 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12078 14

certified_graph_case record017 30 30792005722368 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12079 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00050

module
prelude
public meta import GraphCases
public import GraphInputsRow30Part00008Checked
public import GraphInputsRow30Part00008Metadata
public import GraphInputsRow30Part00008Frames
public import GraphInputsRow30Part00008Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch108
public import GraphCoverageBatch155
public import GraphInputsRow30Part00008Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 30 6065781477632 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10800 14

certified_graph_case record001 30 6066141233152 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10801 14

certified_graph_case record002 30 6067324981264 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10802 14

certified_graph_case record003 30 6086531252480 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10803 14

certified_graph_case record004 30 6086531317760 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10804 14

theorem record005_parameters : Parameters record005 (rowOfCode 30) 6086534893824 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 6086534893824 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10805 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 6086534893824
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch108.candidate10805_checked

theorem record005_result : Result (30, 6086534893824) :=
  of_direct_small 30 6086534893824 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00008.record005.direct_core, record005_parameters, record005_coverage⟩

certified_graph_case record006 30 6087587823872 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10806 14

certified_graph_case record007 30 6087587889152 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10807 14

certified_graph_case record008 30 6099413504256 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15547 14

certified_graph_case record009 30 6099416170496 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10808 14

certified_graph_case record010 30 6099537233936 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10809 14

certified_graph_case record011 30 6100610973697 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10810 14

certified_graph_case record012 30 6339585640464 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10811 14

theorem record013_parameters : Parameters record013 (rowOfCode 30) 6340659380225 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record013_coverage : Coverage record013 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 6340659380225 :=
  GraphCoverageDescriptions.coverage_of_checked record013 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15548 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 6340659380225
    (by rfl) record013_cells_exact
    (GraphCoverageDescriptions.small_allowed record013 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch155.candidate15548_checked

theorem record013_result : Result (30, 6340659380225) :=
  of_direct_small 30 6340659380225 (by decide) ⟨record013, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00008.record013.direct_core, record013_parameters, record013_coverage⟩

certified_graph_case record014 30 6378844323840 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10812 14

certified_graph_case record015 30 6379100340480 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10813 14

certified_graph_case record016 30 6379368808448 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10814 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00008

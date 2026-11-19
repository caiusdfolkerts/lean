module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00139Checked
public import GraphInputsRow29Part00139Metadata
public import GraphInputsRow29Part00139Frames
public import GraphInputsRow29Part00139Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch117
public import GraphCoverageBatch151
public import GraphInputsRow29Part00139Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00139
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 23933740941568 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15136 14

certified_graph_case record001 29 23934511104000 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11721 14

theorem record002_parameters : Parameters record002 (rowOfCode 29) 23940182327552 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 23940182327552 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15137 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 23940182327552
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch151.candidate15137_checked

theorem record002_result : Result (29, 23940182327552) :=
  of_direct_small 29 23940182327552 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00139.record002.direct_core, record002_parameters, record002_coverage⟩

certified_graph_case record003 29 23970212643072 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15138 14

certified_graph_case record004 29 23971017785856 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15139 14

certified_graph_case record005 29 23971563044864 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15140 14

certified_graph_case record006 29 23972091527168 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11722 14

certified_graph_case record007 29 23974507593984 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15141 14

certified_graph_case record008 29 24004643586048 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15142 14

certified_graph_case record009 29 24026609090560 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15143 14

certified_graph_case record010 29 24034658025472 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15144 14

theorem record011_parameters : Parameters record011 (rowOfCode 29) 24035442556928 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record011_coverage : Coverage record011 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24035442556928 :=
  GraphCoverageDescriptions.coverage_of_checked record011 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11723 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24035442556928
    (by rfl) record011_cells_exact
    (GraphCoverageDescriptions.small_allowed record011 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch117.candidate11723_checked

theorem record011_result : Result (29, 24035442556928) :=
  of_direct_small 29 24035442556928 (by decide) ⟨record011, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00139.record011.direct_core, record011_parameters, record011_coverage⟩

certified_graph_case record012 29 24039208779776 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15145 14

certified_graph_case record013 29 24052959871232 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15146 14

certified_graph_case record014 29 24055180754944 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11724 14

theorem record015_parameters : Parameters record015 (rowOfCode 29) 24055717560320 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record015_coverage : Coverage record015 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24055717560320 :=
  GraphCoverageDescriptions.coverage_of_checked record015 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11725 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24055717560320
    (by rfl) record015_cells_exact
    (GraphCoverageDescriptions.small_allowed record015 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch117.candidate11725_checked

theorem record015_result : Result (29, 24055717560320) :=
  of_direct_small 29 24055717560320 (by decide) ⟨record015, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00139.record015.direct_core, record015_parameters, record015_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00139

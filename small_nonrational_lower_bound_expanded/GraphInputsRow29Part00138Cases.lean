module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00138Checked
public import GraphInputsRow29Part00138Metadata
public import GraphInputsRow29Part00138Frames
public import GraphInputsRow29Part00138Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch117
public import GraphCoverageBatch151
public import GraphInputsRow29Part00138Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 23692920815616 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11718 14

certified_graph_case record001 29 23695372386560 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15120 14

certified_graph_case record002 29 23696140468224 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15121 14

certified_graph_case record003 29 23699665256704 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15122 14

certified_graph_case record004 29 23764330938368 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15123 14

certified_graph_case record005 29 23795798704128 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15124 14

certified_graph_case record006 29 23795807027200 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15125 14

certified_graph_case record007 29 23796302020864 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15126 14

certified_graph_case record008 29 23796937981952 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15127 14

certified_graph_case record009 29 23832773722368 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15128 14

certified_graph_case record010 29 23897760071680 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15129 14

certified_graph_case record011 29 23921626251264 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15130 14

certified_graph_case record012 29 23925787000832 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15131 14

theorem record013_parameters : Parameters record013 (rowOfCode 29) 23932700754176 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record013_coverage : Coverage record013 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 23932700754176 :=
  GraphCoverageDescriptions.coverage_of_checked record013 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15132 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 23932700754176
    (by rfl) record013_cells_exact
    (GraphCoverageDescriptions.small_allowed record013 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch151.candidate15132_checked

theorem record013_result : Result (29, 23932700754176) :=
  of_direct_small 29 23932700754176 (by decide) ⟨record013, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00138.record013.direct_core, record013_parameters, record013_coverage⟩

theorem record014_parameters : Parameters record014 (rowOfCode 29) 23932837101568 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record014_coverage : Coverage record014 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 23932837101568 :=
  GraphCoverageDescriptions.coverage_of_checked record014 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15133 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 23932837101568
    (by rfl) record014_cells_exact
    (GraphCoverageDescriptions.small_allowed record014 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch151.candidate15133_checked

theorem record014_result : Result (29, 23932837101568) :=
  of_direct_small 29 23932837101568 (by decide) ⟨record014, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00138.record014.direct_core, record014_parameters, record014_coverage⟩

theorem record015_parameters : Parameters record015 (rowOfCode 29) 23932845424640 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record015_coverage : Coverage record015 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 23932845424640 :=
  GraphCoverageDescriptions.coverage_of_checked record015 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11719 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 23932845424640
    (by rfl) record015_cells_exact
    (GraphCoverageDescriptions.small_allowed record015 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch117.candidate11719_checked

theorem record015_result : Result (29, 23932845424640) :=
  of_direct_small 29 23932845424640 (by decide) ⟨record015, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00138.record015.direct_core, record015_parameters, record015_coverage⟩

certified_graph_case record016 29 23932969222144 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15134 14

certified_graph_case record017 29 23932977545216 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15135 14

certified_graph_case record018 29 23933437886464 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11720 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00138

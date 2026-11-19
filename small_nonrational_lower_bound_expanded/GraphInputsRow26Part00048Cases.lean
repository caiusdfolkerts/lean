module
prelude
public meta import GraphCases
public import GraphInputsRow26Part00048Checked
public import GraphInputsRow26Part00048Metadata
public import GraphInputsRow26Part00048Frames
public import GraphInputsRow26Part00048Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch090
public import GraphCoverageBatch129
public import GraphInputsRow26Part00048Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00048
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 26 24640522043392 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09063 14

certified_graph_case record001 26 24640573409280 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09065 14

certified_graph_case record002 26 24640837650432 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09066 14

certified_graph_case record003 26 24642777514752 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09068 14

certified_graph_case record004 26 24643180167744 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09069 14

certified_graph_case record005 26 24644723949824 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09070 14

certified_graph_case record006 26 24644734158848 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09071 14

certified_graph_case record007 26 24645077057600 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09072 14

certified_graph_case record008 26 24645079154688 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09073 14

certified_graph_case record009 26 24645126602816 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09074 14

certified_graph_case record010 26 24645193703488 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09075 14

certified_graph_case record011 26 24655662416448 GraphCoverageDescriptions.GraphCoverageBatch129.candidate12923 14

certified_graph_case record012 26 24663849844800 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09077 14

certified_graph_case record013 26 24663984062464 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09078 14

certified_graph_case record014 26 24663986143232 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09079 14

theorem record015_parameters : Parameters record015 (rowOfCode 26) 24665997320256 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record015_coverage : Coverage record015 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24665997320256 :=
  GraphCoverageDescriptions.coverage_of_checked record015 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09080 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24665997320256
    (by rfl) record015_cells_exact
    (GraphCoverageDescriptions.small_allowed record015 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch090.candidate09080_checked

theorem record015_result : Result (26, 24665997320256) :=
  of_direct_small 26 24665997320256 (by decide) ⟨record015, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00048.record015.direct_core, record015_parameters, record015_coverage⟩

theorem record016_parameters : Parameters record016 (rowOfCode 26) 24666064437248 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record016_coverage : Coverage record016 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24666064437248 :=
  GraphCoverageDescriptions.coverage_of_checked record016 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09081 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24666064437248
    (by rfl) record016_cells_exact
    (GraphCoverageDescriptions.small_allowed record016 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch090.candidate09081_checked

theorem record016_result : Result (26, 24666064437248) :=
  of_direct_small 26 24666064437248 (by decide) ⟨record016, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00048.record016.direct_core, record016_parameters, record016_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00048

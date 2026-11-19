module
prelude
public meta import GraphCases
public import GraphInputsRow26Part00033Checked
public import GraphInputsRow26Part00033Metadata
public import GraphInputsRow26Part00033Frames
public import GraphInputsRow26Part00033Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch080
public import GraphCoverageBatch081
public import GraphCoverageBatch128
public import GraphInputsRow26Part00033Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00033
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 26 19595324882944 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08075 14

certified_graph_case record001 26 19595331125248 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08076 14

certified_graph_case record002 26 19596360843520 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08078 14

certified_graph_case record003 26 19596365070336 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08079 14

certified_graph_case record004 26 19602341890176 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08080 14

certified_graph_case record005 26 19611963654400 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08082 14

certified_graph_case record006 26 19612100001792 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08083 14

certified_graph_case record007 26 19612108324864 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08084 14

certified_graph_case record008 26 19612232122368 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08085 14

certified_graph_case record009 26 19612240445440 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08086 14

certified_graph_case record010 26 19612504686592 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08087 14

theorem record011_parameters : Parameters record011 (rowOfCode 26) 19612700786688 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record011_coverage : Coverage record011 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 19612700786688 :=
  GraphCoverageDescriptions.coverage_of_checked record011 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08088 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 19612700786688
    (by rfl) record011_cells_exact
    (GraphCoverageDescriptions.small_allowed record011 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch080.candidate08088_checked

theorem record011_result : Result (26, 19612700786688) :=
  of_direct_small 26 19612700786688 (by decide) ⟨record011, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00033.record011.direct_core, record011_parameters, record011_coverage⟩

certified_graph_case record012 26 19612768927744 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08089 14

certified_graph_case record013 26 19623709967368 GraphCoverageDescriptions.GraphCoverageBatch128.candidate12843 14

certified_graph_case record014 26 19628556321024 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08098 14

certified_graph_case record015 26 19628560547840 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08099 14

certified_graph_case record016 26 19628566790144 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08100 14

certified_graph_case record017 26 19628684216320 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08102 14

certified_graph_case record018 26 19632970858496 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08104 14

certified_graph_case record019 26 19636733216896 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08105 14

certified_graph_case record020 26 19646004592640 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08107 14

certified_graph_case record021 26 19649744011264 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08108 14

certified_graph_case record022 26 19649752334336 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08109 14

certified_graph_case record023 26 19657404776448 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08111 14

certified_graph_case record024 26 19657664790784 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08112 14

certified_graph_case record025 26 19657675259904 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08113 14

certified_graph_case record026 26 19659485151232 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08114 14

certified_graph_case record027 26 19664048504832 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08116 14

theorem record028_parameters : Parameters record028 (rowOfCode 26) 19680825704448 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record028_coverage : Coverage record028 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 19680825704448 :=
  GraphCoverageDescriptions.coverage_of_checked record028 GraphCoverageDescriptions.GraphCoverageBatch081.candidate08119 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 19680825704448
    (by rfl) record028_cells_exact
    (GraphCoverageDescriptions.small_allowed record028 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch081.candidate08119_checked

theorem record028_result : Result (26, 19680825704448) :=
  of_direct_small 26 19680825704448 (by decide) ⟨record028, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00033.record028.direct_core, record028_parameters, record028_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00033

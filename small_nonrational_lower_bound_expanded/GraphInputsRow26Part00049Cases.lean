module
prelude
public meta import GraphCases
public import GraphInputsRow26Part00049Checked
public import GraphInputsRow26Part00049Metadata
public import GraphInputsRow26Part00049Frames
public import GraphInputsRow26Part00049Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch090
public import GraphCoverageBatch091
public import GraphCoverageBatch129
public import GraphInputsRow26Part00049Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00049
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 26) 24666066518016 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24666066518016 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09082 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24666066518016
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch090.candidate09082_checked

theorem record000_result : Result (26, 24666066518016) :=
  of_direct_small 26 24666066518016 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00049.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 26 24666198508032 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09083 14

theorem record002_parameters : Parameters record002 (rowOfCode 26) 24672734298112 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24672734298112 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09085 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24672734298112
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch090.candidate09085_checked

theorem record002_result : Result (26, 24672734298112) :=
  of_direct_small 26 24672734298112 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00049.record002.direct_core, record002_parameters, record002_coverage⟩

certified_graph_case record003 26 24676940185600 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09087 14

certified_graph_case record004 26 24681633546816 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09088 14

theorem record005_parameters : Parameters record005 (rowOfCode 26) 24739097907472 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24739097907472 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch129.candidate12924 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24739097907472
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch129.candidate12924_checked

theorem record005_result : Result (26, 24739097907472) :=
  of_direct_small 26 24739097907472 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00049.record005.direct_core, record005_parameters, record005_coverage⟩

certified_graph_case record006 26 24740154738960 GraphCoverageDescriptions.GraphCoverageBatch129.candidate12925 14

certified_graph_case record007 26 24740245348480 GraphCoverageDescriptions.GraphCoverageBatch129.candidate12926 14

certified_graph_case record008 26 24741319086208 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09089 14

certified_graph_case record009 26 24743415976064 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09095 14

certified_graph_case record010 26 24748986745088 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09097 14

certified_graph_case record011 26 24748986810368 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09098 14

certified_graph_case record012 26 24749087396096 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09099 14

certified_graph_case record013 26 24779017060608 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09108 14

certified_graph_case record014 26 24779017125888 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09109 14

certified_graph_case record015 26 24779146985728 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09110 14

certified_graph_case record016 26 24782519681280 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09112 14

certified_graph_case record017 26 24782519746560 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09113 14

certified_graph_case record018 26 24782521241856 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09114 14

certified_graph_case record019 26 24810172743936 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09117 14

certified_graph_case record020 26 24826388447488 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09118 14

certified_graph_case record021 26 24827461665024 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09119 14

certified_graph_case record022 26 24855583981568 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09122 14

certified_graph_case record023 26 24885603082304 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09129 14

certified_graph_case record024 26 24885603098624 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09130 14

certified_graph_case record025 26 24885603602496 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09131 14

certified_graph_case record026 26 24885654980624 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09132 14

certified_graph_case record027 26 24894042540048 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09136 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00049

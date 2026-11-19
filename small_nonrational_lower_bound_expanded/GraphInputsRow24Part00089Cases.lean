module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00089Checked
public import GraphInputsRow24Part00089Metadata
public import GraphInputsRow24Part00089Frames
public import GraphInputsRow24Part00089Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch090
public import GraphCoverageBatch091
public import GraphInputsRow24Part00089Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00089
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 24681633546816 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09088 14

certified_graph_case record001 24 24741319086208 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09089 14

certified_graph_case record002 24 24741335601280 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09090 14

certified_graph_case record003 24 24742413303808 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09091 14

certified_graph_case record004 24 24742541197568 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09092 14

certified_graph_case record005 24 24742648090880 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09093 14

certified_graph_case record006 24 24743050743872 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09094 14

certified_graph_case record007 24 24743415976064 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09095 14

certified_graph_case record008 24 24748980502784 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09096 14

certified_graph_case record009 24 24748986745088 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09097 14

certified_graph_case record010 24 24748986810368 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09098 14

certified_graph_case record011 24 24749087396096 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09099 14

certified_graph_case record012 24 24749248970752 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09100 14

certified_graph_case record013 24 24749258317888 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09101 14

certified_graph_case record014 24 24749291868224 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09102 14

certified_graph_case record015 24 24757607076096 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09103 14

certified_graph_case record016 24 24777956327680 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09104 14

certified_graph_case record017 24 24777960554496 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09105 14

certified_graph_case record018 24 24778484221968 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09106 14

certified_graph_case record019 24 24779012899072 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09107 14

certified_graph_case record020 24 24779017060608 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09108 14

certified_graph_case record021 24 24779017125888 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09109 14

certified_graph_case record022 24 24779146985728 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09110 14

certified_graph_case record023 24 24779557961729 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09111 14

theorem record024_parameters : Parameters record024 (rowOfCode 24) 24782519681280 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record024_coverage : Coverage record024 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24782519681280 :=
  GraphCoverageDescriptions.coverage_of_checked record024 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09112 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24782519681280
    (by rfl) record024_cells_exact
    (GraphCoverageDescriptions.small_allowed record024 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch091.candidate09112_checked

theorem record024_result : Result (24, 24782519681280) :=
  of_direct_small 24 24782519681280 (by decide) ⟨record024, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00089.record024.direct_core, record024_parameters, record024_coverage⟩

theorem record025_parameters : Parameters record025 (rowOfCode 24) 24782519746560 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record025_coverage : Coverage record025 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24782519746560 :=
  GraphCoverageDescriptions.coverage_of_checked record025 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09113 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24782519746560
    (by rfl) record025_cells_exact
    (GraphCoverageDescriptions.small_allowed record025 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch091.candidate09113_checked

theorem record025_result : Result (24, 24782519746560) :=
  of_direct_small 24 24782519746560 (by decide) ⟨record025, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00089.record025.direct_core, record025_parameters, record025_coverage⟩

theorem record026_parameters : Parameters record026 (rowOfCode 24) 24782521241856 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record026_coverage : Coverage record026 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24782521241856 :=
  GraphCoverageDescriptions.coverage_of_checked record026 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09114 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24782521241856
    (by rfl) record026_cells_exact
    (GraphCoverageDescriptions.small_allowed record026 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch091.candidate09114_checked

theorem record026_result : Result (24, 24782521241856) :=
  of_direct_small 24 24782521241856 (by decide) ⟨record026, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00089.record026.direct_core, record026_parameters, record026_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00089

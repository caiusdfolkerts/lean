module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00144Checked
public import GraphInputsRow29Part00144Metadata
public import GraphInputsRow29Part00144Frames
public import GraphInputsRow29Part00144Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch151
public import GraphInputsRow29Part00144Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00144
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 24303879913472 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15159 14

theorem record001_parameters : Parameters record001 (rowOfCode 29) 24305828167680 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24305828167680 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15160 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24305828167680
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch151.candidate15160_checked

theorem record001_result : Result (29, 24305828167680) :=
  of_direct_small 29 24305828167680 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00144.record001.direct_core, record001_parameters, record001_coverage⟩

certified_graph_case record002 29 24312333468288 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15161 14

certified_graph_case record003 29 24335847268416 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15162 14

certified_graph_case record004 29 24336903839808 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15163 14

theorem record005_parameters : Parameters record005 (rowOfCode 29) 24345352093952 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24345352093952 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15164 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24345352093952
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch151.candidate15164_checked

theorem record005_result : Result (29, 24345352093952) :=
  of_direct_small 29 24345352093952 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00144.record005.direct_core, record005_parameters, record005_coverage⟩

certified_graph_case record006 29 24345361522688 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15165 14

certified_graph_case record007 29 24345754746944 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15166 14

certified_graph_case record008 29 24372473495552 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15167 14

theorem record009_parameters : Parameters record009 (rowOfCode 29) 24380786671616 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24380786671616 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15168 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24380786671616
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.small_allowed record009 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch151.candidate15168_checked

theorem record009_result : Result (29, 24380786671616) :=
  of_direct_small 29 24380786671616 (by decide) ⟨record009, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00144.record009.direct_core, record009_parameters, record009_coverage⟩

certified_graph_case record010 29 24380794994688 GraphCoverageDescriptions.GraphCoverageBatch151.candidate15169 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00144

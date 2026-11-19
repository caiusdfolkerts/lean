module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00089Checked
public import GraphInputsRow29Part00089Metadata
public import GraphInputsRow29Part00089Frames
public import GraphInputsRow29Part00089Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch113
public import GraphCoverageBatch147
public import GraphInputsRow29Part00089Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00089
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 29) 15679382634624 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 15679382634624 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11376 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 15679382634624
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch113.candidate11376_checked

theorem record000_result : Result (29, 15679382634624) :=
  of_direct_small 29 15679382634624 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00089.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 29 15705760104704 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14732 14

certified_graph_case record002 29 15706296975360 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14733 14

certified_graph_case record003 29 15706429095936 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14734 14

certified_graph_case record004 29 15712410140672 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11377 14

theorem record005_parameters : Parameters record005 (rowOfCode 29) 15712670220288 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 15712670220288 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11378 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 15712670220288
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch113.candidate11378_checked

theorem record005_result : Result (29, 15712670220288) :=
  of_direct_small 29 15712670220288 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00089.record005.direct_core, record005_parameters, record005_coverage⟩

certified_graph_case record006 29 15722939973632 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14735 14

certified_graph_case record007 29 15723208376320 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11379 14

theorem record008_parameters : Parameters record008 (rowOfCode 29) 15809306984448 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 15809306984448 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11380 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 15809306984448
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch113.candidate11380_checked

theorem record008_result : Result (29, 15809306984448) :=
  of_direct_small 29 15809306984448 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00089.record008.direct_core, record008_parameters, record008_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00089

module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00176Checked
public import GraphInputsRow31Part00176Metadata
public import GraphInputsRow31Part00176Frames
public import GraphInputsRow31Part00176Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch169
public import GraphInputsRow31Part00176Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00176
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 34713536299008 GraphCoverageDescriptions.GraphCoverageBatch169.candidate16923 14

certified_graph_case record001 31 34729139109888 GraphCoverageDescriptions.GraphCoverageBatch169.candidate16924 14

certified_graph_case record002 31 34772072595456 GraphCoverageDescriptions.GraphCoverageBatch169.candidate16925 14

certified_graph_case record003 31 34789252399104 GraphCoverageDescriptions.GraphCoverageBatch169.candidate16926 14

certified_graph_case record004 31 34790308970496 GraphCoverageDescriptions.GraphCoverageBatch169.candidate16927 14

certified_graph_case record005 31 34840799870976 GraphCoverageDescriptions.GraphCoverageBatch169.candidate16928 14

certified_graph_case record006 31 34909494315024 GraphCoverageDescriptions.GraphCoverageBatch169.candidate16929 14

certified_graph_case record007 31 35046933268480 GraphCoverageDescriptions.GraphCoverageBatch169.candidate16930 14

theorem record008_parameters : Parameters record008 (rowOfCode 31) 35115669389312 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 35115669389312 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch169.candidate16931 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 35115669389312
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch169.candidate16931_checked

theorem record008_result : Result (31, 35115669389312) :=
  of_direct_small 31 35115669389312 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00176.record008.direct_core, record008_parameters, record008_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00176

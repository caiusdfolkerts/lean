module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00117Checked
public import GraphInputsRow29Part00117Metadata
public import GraphInputsRow29Part00117Frames
public import GraphInputsRow29Part00117Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch115
public import GraphCoverageBatch116
public import GraphCoverageBatch149
public import GraphInputsRow29Part00117Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00117
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 20199436713984 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11596 14

certified_graph_case record001 29 20278893674496 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11597 14

certified_graph_case record002 29 20346675663104 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14942 14

certified_graph_case record003 29 20381100474624 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14943 14

certified_graph_case record004 29 20381368877312 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14944 14

certified_graph_case record005 29 20381377265664 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11598 14

certified_graph_case record006 29 20385670135808 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11599 14

certified_graph_case record007 29 20388881400064 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14945 14

theorem record008_parameters : Parameters record008 (rowOfCode 29) 20393991634944 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 20393991634944 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11600 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 20393991634944
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch116.candidate11600_checked

theorem record008_result : Result (29, 20393991634944) :=
  of_direct_small 29 20393991634944 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00117.record008.direct_core, record008_parameters, record008_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00117

module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00044Checked
public import GraphInputsRow29Part00044Metadata
public import GraphInputsRow29Part00044Frames
public import GraphInputsRow29Part00044Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch109
public import GraphCoverageBatch144
public import GraphInputsRow29Part00044Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00044
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 7821953335296 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10972 14

certified_graph_case record001 29 7890538594304 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10973 14

certified_graph_case record002 29 7989924757504 GraphCoverageDescriptions.GraphCoverageBatch144.candidate14459 14

certified_graph_case record003 29 8019387613184 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10974 14

certified_graph_case record004 29 8027964965504 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10975 14

theorem record005_parameters : Parameters record005 (rowOfCode 29) 8041454141696 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8041454141696 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10976 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8041454141696
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch109.candidate10976_checked

theorem record005_result : Result (29, 8041454141696) :=
  of_direct_small 29 8041454141696 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00044.record005.direct_core, record005_parameters, record005_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00044

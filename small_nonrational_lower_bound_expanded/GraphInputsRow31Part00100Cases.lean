module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00100Checked
public import GraphInputsRow31Part00100Metadata
public import GraphInputsRow31Part00100Frames
public import GraphInputsRow31Part00100Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch164
public import GraphInputsRow31Part00100Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00100
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 22043462483968 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16466 14

certified_graph_case record001 31 22064925802752 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16467 14

theorem record002_parameters : Parameters record002 (rowOfCode 31) 22077408051456 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 22077408051456 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16468 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 22077408051456
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch164.candidate16468_checked

theorem record002_result : Result (31, 22077408051456) :=
  of_direct_small 31 22077408051456 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00100.record002.direct_core, record002_parameters, record002_coverage⟩

certified_graph_case record003 31 22146538553344 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16469 14

certified_graph_case record004 31 22179774218240 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16470 14

certified_graph_case record005 31 22182166069248 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16471 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00100

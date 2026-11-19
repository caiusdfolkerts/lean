module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00160Checked
public import GraphInputsRow31Part00160Metadata
public import GraphInputsRow31Part00160Frames
public import GraphInputsRow31Part00160Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch168
public import GraphInputsRow31Part00160Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00160
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 31512451940352 GraphCoverageDescriptions.GraphCoverageBatch168.candidate16825 14

certified_graph_case record001 31 31521310244864 GraphCoverageDescriptions.GraphCoverageBatch168.candidate16826 14

theorem record002_parameters : Parameters record002 (rowOfCode 31) 31525613601280 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31525613601280 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch168.candidate16827 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 31525613601280
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch168.candidate16827_checked

theorem record002_result : Result (31, 31525613601280) :=
  of_direct_small 31 31525613601280 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00160.record002.direct_core, record002_parameters, record002_coverage⟩

certified_graph_case record003 31 31529631744000 GraphCoverageDescriptions.GraphCoverageBatch168.candidate16828 14

certified_graph_case record004 31 31530160226304 GraphCoverageDescriptions.GraphCoverageBatch168.candidate16829 14

certified_graph_case record005 31 31533650083840 GraphCoverageDescriptions.GraphCoverageBatch168.candidate16830 14

certified_graph_case record006 31 31568085123072 GraphCoverageDescriptions.GraphCoverageBatch168.candidate16831 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00160

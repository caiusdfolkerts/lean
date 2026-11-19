module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00033Checked
public import GraphInputsRow31Part00033Metadata
public import GraphInputsRow31Part00033Frames
public import GraphInputsRow31Part00033Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch158
public import GraphInputsRow31Part00033Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00033
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 31) 7206990807296 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 7206990807296 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15885 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 7206990807296
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch158.candidate15885_checked

theorem record000_result : Result (31, 7206990807296) :=
  of_direct_small 31 7206990807296 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00033.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 31 7275674763520 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15886 14

certified_graph_case record002 31 7276479906304 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15887 14

certified_graph_case record003 31 7276488294400 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15888 14

certified_graph_case record004 31 7291512881152 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15889 14

certified_graph_case record005 31 7294542675968 GraphCoverageDescriptions.GraphCoverageBatch158.candidate15890 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00033

module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00075Checked
public import GraphInputsRow31Part00075Metadata
public import GraphInputsRow31Part00075Frames
public import GraphInputsRow31Part00075Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch161
public import GraphInputsRow31Part00075Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00075
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 14299602886656 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16194 14

theorem record001_parameters : Parameters record001 (rowOfCode 31) 14303895756800 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 14303895756800 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16195 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 14303895756800
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch161.candidate16195_checked

theorem record001_result : Result (31, 14303895756800) :=
  of_direct_small 31 14303895756800 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00075.record001.direct_core, record001_parameters, record001_coverage⟩

certified_graph_case record002 31 14347373936896 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16196 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00075

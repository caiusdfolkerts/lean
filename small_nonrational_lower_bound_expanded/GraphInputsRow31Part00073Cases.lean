module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00073Checked
public import GraphInputsRow31Part00073Metadata
public import GraphInputsRow31Part00073Frames
public import GraphInputsRow31Part00073Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch161
public import GraphInputsRow31Part00073Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00073
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 13900393218592 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16177 14

certified_graph_case record001 31 13900394332160 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16178 14

certified_graph_case record002 31 13933431816192 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16179 14

certified_graph_case record003 31 13933440139264 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16180 14

certified_graph_case record004 31 13941740732416 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16181 14

certified_graph_case record005 31 13942277537792 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16182 14

theorem record006_parameters : Parameters record006 (rowOfCode 31) 14027648934144 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 14027648934144 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16183 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 14027648934144
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch161.candidate16183_checked

theorem record006_result : Result (31, 14027648934144) :=
  of_direct_small 31 14027648934144 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00073.record006.direct_core, record006_parameters, record006_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00073

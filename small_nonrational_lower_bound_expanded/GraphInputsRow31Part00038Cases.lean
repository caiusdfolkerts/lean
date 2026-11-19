module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00038Checked
public import GraphInputsRow31Part00038Metadata
public import GraphInputsRow31Part00038Frames
public import GraphInputsRow31Part00038Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch159
public import GraphInputsRow31Part00038Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00038
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 7606387277824 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15924 14

certified_graph_case record001 31 7606932340736 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15925 14

certified_graph_case record002 31 7615253839872 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15926 14

certified_graph_case record003 31 7623567081472 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15927 14

certified_graph_case record004 31 7624103821312 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15928 14

theorem record005_parameters : Parameters record005 (rowOfCode 31) 7736985190400 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 7736985190400 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15929 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 7736985190400
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch159.candidate15929_checked

theorem record005_result : Result (31, 7736985190400) :=
  of_direct_small 31 7736985190400 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00038.record005.direct_core, record005_parameters, record005_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00038

module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00290Checked
public import GraphInputsRow29Part00290Metadata
public import GraphInputsRow29Part00290Frames
public import GraphInputsRow29Part00290Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch123
public import GraphInputsRow29Part00290Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00290
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 34712479858688 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12350 14

certified_graph_case record001 29 34712999624704 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12351 14

theorem record002_parameters : Parameters record002 (rowOfCode 29) 34729105690624 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34729105690624 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch123.candidate12352 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 34729105690624
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch123.candidate12352_checked

theorem record002_result : Result (29, 34729105690624) :=
  of_direct_small 29 34729105690624 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00290.record002.direct_core, record002_parameters, record002_coverage⟩
#print axioms record002_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00290

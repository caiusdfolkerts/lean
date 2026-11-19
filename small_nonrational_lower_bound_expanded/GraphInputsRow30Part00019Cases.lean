module
prelude
public meta import GraphCases
public import GraphInputsRow30Part00019Checked
public import GraphInputsRow30Part00019Metadata
public import GraphInputsRow30Part00019Frames
public import GraphInputsRow30Part00019Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch110
public import GraphInputsRow30Part00019Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00019
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 30 10484309393408 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11080 14

theorem record001_parameters : Parameters record001 (rowOfCode 30) 10484312969472 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10484312969472 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11081 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10484312969472
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch110.candidate11081_checked

theorem record001_result : Result (30, 10484312969472) :=
  of_direct_small 30 10484312969472 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00019.record001.direct_core, record001_parameters, record001_coverage⟩

certified_graph_case record002 30 10488604344320 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11082 14

certified_graph_case record003 30 10488605839616 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11083 14

certified_graph_case record004 30 10488868585472 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11084 14

certified_graph_case record005 30 10488870080768 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11085 14

certified_graph_case record006 30 10488993810448 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11086 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00019

module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00013Checked
public import GraphInputsRow31Part00013Metadata
public import GraphInputsRow31Part00013Frames
public import GraphInputsRow31Part00013Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch157
public import GraphInputsRow31Part00013Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00013
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 3415174348800 GraphCoverageDescriptions.GraphCoverageBatch157.candidate15715 14

certified_graph_case record001 31 3736757895424 GraphCoverageDescriptions.GraphCoverageBatch157.candidate15716 14

theorem record002_parameters : Parameters record002 (rowOfCode 31) 3922651578624 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 3922651578624 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch157.candidate15717 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 3922651578624
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch157.candidate15717_checked

theorem record002_result : Result (31, 3922651578624) :=
  of_direct_small 31 3922651578624 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00013.record002.direct_core, record002_parameters, record002_coverage⟩
#print axioms record002_result

certified_graph_case record003 31 3923188449280 GraphCoverageDescriptions.GraphCoverageBatch157.candidate15718 14

certified_graph_case record004 31 3923196772352 GraphCoverageDescriptions.GraphCoverageBatch157.candidate15719 14

certified_graph_case record005 31 3926812328192 GraphCoverageDescriptions.GraphCoverageBatch157.candidate15720 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00013

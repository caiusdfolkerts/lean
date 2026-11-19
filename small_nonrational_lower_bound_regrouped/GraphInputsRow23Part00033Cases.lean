module
prelude
public meta import GraphCases
public import GraphInputsRow23Part00033Checked
public import GraphInputsRow23Part00033Metadata
public import GraphInputsRow23Part00033Frames
public import GraphInputsRow23Part00033Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch060
public import GraphInputsRow23Part00033Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00033
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 23 33719788437504 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06051 6

certified_graph_case record001 23 33751002251264 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06052 6

certified_graph_case record002 23 33751530733568 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06053 6

certified_graph_case record003 23 34088117371136 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06054 6

certified_graph_case record004 23 34088253718528 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06055 6

certified_graph_case record005 23 34088262041600 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06056 6

certified_graph_case record006 23 34088385839104 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06057 6

certified_graph_case record007 23 34088394162176 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06058 6

certified_graph_case record008 23 34088484929536 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06059 6

certified_graph_case record009 23 34088887533568 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06060 6

certified_graph_case record010 23 34091337023744 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06061 6

certified_graph_case record011 23 34092108746752 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06062 6

certified_graph_case record012 23 34094558757120 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06063 6

certified_graph_case record013 23 34094726053888 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06064 6

certified_graph_case record014 23 34095095627776 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06065 6

theorem record015_parameters : Parameters record015 (rowOfCode 23) 34095097708544 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record015_coverage : Coverage record015 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34095097708544 :=
  GraphCoverageDescriptions.coverage_of_checked record015 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06066 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 34095097708544
    (by rfl) record015_cells_exact
    (GraphCoverageDescriptions.small_allowed record015 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch060.candidate06066_checked

theorem record015_result : Result (23, 34095097708544) :=
  of_direct_small 23 34095097708544 (by decide) ⟨record015, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00033.record015.direct_core, record015_parameters, record015_coverage⟩
#print axioms record015_result

certified_graph_case record016 23 34095128657920 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06067 6

certified_graph_case record017 23 34095631974656 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06068 6

certified_graph_case record018 23 34096269496320 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06069 6

certified_graph_case record019 23 34110664351808 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06070 6

certified_graph_case record020 23 34123532501248 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06071 6

certified_graph_case record021 23 34123800969216 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06072 6

certified_graph_case record022 23 34123809292288 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06073 6

certified_graph_case record023 23 34124320739328 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06074 6

certified_graph_case record024 23 34124589072640 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06075 6

theorem record025_parameters : Parameters record025 (rowOfCode 23) 34124865863680 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record025_coverage : Coverage record025 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34124865863680 :=
  GraphCoverageDescriptions.coverage_of_checked record025 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06076 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 34124865863680
    (by rfl) record025_cells_exact
    (GraphCoverageDescriptions.small_allowed record025 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch060.candidate06076_checked

theorem record025_result : Result (23, 34124865863680) :=
  of_direct_small 23 34124865863680 (by decide) ⟨record025, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00033.record025.direct_core, record025_parameters, record025_coverage⟩
#print axioms record025_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00033

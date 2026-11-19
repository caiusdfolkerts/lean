module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00090Checked
public import GraphInputsRow31Part00090Metadata
public import GraphInputsRow31Part00090Frames
public import GraphInputsRow31Part00090Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch163
public import GraphInputsRow31Part00090Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00090
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 17748224647232 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16369 14

theorem record001_parameters : Parameters record001 (rowOfCode 31) 17775403728897 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 17775403728897 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16370 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 17775403728897
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch163.candidate16370_checked

theorem record001_result : Result (31, 17775403728897) :=
  of_direct_small 31 17775403728897 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00090.record001.direct_core, record001_parameters, record001_coverage⟩

certified_graph_case record002 31 17775403794432 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16371 14

certified_graph_case record003 31 17777484169216 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16372 14

certified_graph_case record004 31 17783725228033 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16373 14

certified_graph_case record005 31 17783993696256 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16374 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00090

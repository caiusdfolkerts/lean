module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00072Checked
public import GraphInputsRow29Part00072Metadata
public import GraphInputsRow29Part00072Frames
public import GraphInputsRow29Part00072Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch112
public import GraphCoverageBatch146
public import GraphInputsRow29Part00072Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00072
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 12512519061504 GraphCoverageDescriptions.GraphCoverageBatch146.candidate14626 14

certified_graph_case record001 29 12545754726400 GraphCoverageDescriptions.GraphCoverageBatch146.candidate14627 14

theorem record002_parameters : Parameters record002 (rowOfCode 29) 12546270855168 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 12546270855168 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch112.candidate11214 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 12546270855168
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch112.candidate11214_checked

theorem record002_result : Result (29, 12546270855168) :=
  of_direct_small 29 12546270855168 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00072.record002.direct_core, record002_parameters, record002_coverage⟩

certified_graph_case record003 29 12554600448000 GraphCoverageDescriptions.GraphCoverageBatch112.candidate11215 14

theorem record004_parameters : Parameters record004 (rowOfCode 29) 12577830633728 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 12577830633728 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch112.candidate11216 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 12577830633728
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch112.candidate11216_checked

theorem record004_result : Result (29, 12577830633728) :=
  of_direct_small 29 12577830633728 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00072.record004.direct_core, record004_parameters, record004_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00072

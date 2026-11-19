module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00164Checked
public import GraphInputsRow29Part00164Metadata
public import GraphInputsRow29Part00164Frames
public import GraphInputsRow29Part00164Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch118
public import GraphInputsRow29Part00164Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00164
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 29) 25375954436096 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25375954436096 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11818 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25375954436096
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch118.candidate11818_checked

theorem record000_result : Result (29, 25375954436096) :=
  of_direct_small 29 25375954436096 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00164.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 29 25376078233600 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11819 14

certified_graph_case record002 29 25376086556672 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11820 14

certified_graph_case record003 29 25376350797824 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11821 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00164

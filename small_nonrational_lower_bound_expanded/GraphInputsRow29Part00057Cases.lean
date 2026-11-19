module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00057Checked
public import GraphInputsRow29Part00057Metadata
public import GraphInputsRow29Part00057Frames
public import GraphInputsRow29Part00057Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch110
public import GraphCoverageBatch145
public import GraphInputsRow29Part00057Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00057
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 10859097098240 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11095 14

certified_graph_case record001 29 10861037027584 GraphCoverageDescriptions.GraphCoverageBatch145.candidate14561 14

certified_graph_case record002 29 10876537044992 GraphCoverageDescriptions.GraphCoverageBatch145.candidate14562 14

theorem record003_parameters : Parameters record003 (rowOfCode 29) 10892192579584 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10892192579584 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11096 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10892192579584
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch110.candidate11096_checked

theorem record003_result : Result (29, 10892192579584) :=
  of_direct_small 29 10892192579584 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00057.record003.direct_core, record003_parameters, record003_coverage⟩

certified_graph_case record004 29 10892439980288 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11097 14

theorem record005_parameters : Parameters record005 (rowOfCode 29) 10896600598784 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10896600598784 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11098 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10896600598784
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch110.candidate11098_checked

theorem record005_result : Result (29, 10896600598784) :=
  of_direct_small 29 10896600598784 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00057.record005.direct_core, record005_parameters, record005_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00057

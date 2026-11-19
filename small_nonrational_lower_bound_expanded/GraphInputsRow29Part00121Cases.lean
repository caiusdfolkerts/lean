module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00121Checked
public import GraphInputsRow29Part00121Metadata
public import GraphInputsRow29Part00121Frames
public import GraphInputsRow29Part00121Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch116
public import GraphCoverageBatch149
public import GraphInputsRow29Part00121Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00121
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 29) 20724022804480 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 20724022804480 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11613 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 20724022804480
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch116.candidate11613_checked

theorem record000_result : Result (29, 20724022804480) :=
  of_direct_small 29 20724022804480 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00121.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 29 20727531077888 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14978 14

certified_graph_case record002 29 20727807868928 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11614 14

theorem record003_parameters : Parameters record003 (rowOfCode 29) 20727915151360 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 20727915151360 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11615 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 20727915151360
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch116.candidate11615_checked

theorem record003_result : Result (29, 20727915151360) :=
  of_direct_small 29 20727915151360 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00121.record003.direct_core, record003_parameters, record003_coverage⟩

certified_graph_case record004 29 20728067948544 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14979 14

certified_graph_case record005 29 20728072110080 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11616 14

theorem record006_parameters : Parameters record006 (rowOfCode 29) 20728183554048 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 20728183554048 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11617 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 20728183554048
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch116.candidate11617_checked

theorem record006_result : Result (29, 20728183554048) :=
  of_direct_small 29 20728183554048 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00121.record006.direct_core, record006_parameters, record006_coverage⟩

certified_graph_case record007 29 20731807301888 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14980 14

certified_graph_case record008 29 20732612444672 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11618 14

certified_graph_case record009 29 20736121012352 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14981 14

theorem record010_parameters : Parameters record010 (rowOfCode 29) 20736505053184 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record010_coverage : Coverage record010 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 20736505053184 :=
  GraphCoverageDescriptions.coverage_of_checked record010 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11619 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 20736505053184
    (by rfl) record010_cells_exact
    (GraphCoverageDescriptions.small_allowed record010 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch116.candidate11619_checked

theorem record010_result : Result (29, 20736505053184) :=
  of_direct_small 29 20736505053184 (by decide) ⟨record010, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00121.record010.direct_core, record010_parameters, record010_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00121

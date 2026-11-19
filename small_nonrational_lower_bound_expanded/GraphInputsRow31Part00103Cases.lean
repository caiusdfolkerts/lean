module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00103Checked
public import GraphInputsRow31Part00103Metadata
public import GraphInputsRow31Part00103Frames
public import GraphInputsRow31Part00103Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch164
public import GraphInputsRow31Part00103Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 23424888012800 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16489 14

certified_graph_case record001 31 23455622758400 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16490 14

certified_graph_case record002 31 23459180642304 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16491 14

theorem record003_parameters : Parameters record003 (rowOfCode 31) 23504344908032 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 23504344908032 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16492 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 23504344908032
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch164.candidate16492_checked

theorem record003_result : Result (31, 23504344908032) :=
  of_direct_small 31 23504344908032 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00103.record003.direct_core, record003_parameters, record003_coverage⟩

certified_graph_case record004 31 23768894275584 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16493 14

certified_graph_case record005 31 23971017785344 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16494 14

certified_graph_case record006 31 23974650052608 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16495 14

certified_graph_case record007 31 24043763793920 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16496 14

theorem record008_parameters : Parameters record008 (rowOfCode 31) 24054107013120 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24054107013120 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16497 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24054107013120
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch164.candidate16497_checked

theorem record008_result : Result (31, 24054107013120) :=
  of_direct_small 31 24054107013120 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00103.record008.direct_core, record008_parameters, record008_coverage⟩

certified_graph_case record009 31 24091016822784 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16498 14

certified_graph_case record010 31 24108188303360 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16499 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00103

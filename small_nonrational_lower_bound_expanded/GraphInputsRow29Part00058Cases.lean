module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00058Checked
public import GraphInputsRow29Part00058Metadata
public import GraphInputsRow29Part00058Frames
public import GraphInputsRow29Part00058Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch110
public import GraphCoverageBatch111
public import GraphCoverageBatch145
public import GraphInputsRow29Part00058Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00058
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 29) 10896617243392 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10896617243392 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11099 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10896617243392
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch110.candidate11099_checked

theorem record000_result : Result (29, 10896617243392) :=
  of_direct_small 29 10896617243392 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00058.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 29 10896889937920 GraphCoverageDescriptions.GraphCoverageBatch145.candidate14563 14

certified_graph_case record002 29 10896898260992 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11100 14

certified_graph_case record003 29 10897137664000 GraphCoverageDescriptions.GraphCoverageBatch145.candidate14564 14

theorem record004_parameters : Parameters record004 (rowOfCode 29) 10901191131136 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10901191131136 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11101 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10901191131136
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch111.candidate11101_checked

theorem record004_result : Result (29, 10901191131136) :=
  of_direct_small 29 10901191131136 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00058.record004.direct_core, record004_parameters, record004_coverage⟩

certified_graph_case record005 29 10901298413568 GraphCoverageDescriptions.GraphCoverageBatch145.candidate14565 14

certified_graph_case record006 29 10905735659520 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11102 14

certified_graph_case record007 29 10909235839232 GraphCoverageDescriptions.GraphCoverageBatch145.candidate14566 14

certified_graph_case record008 29 10909619912704 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11103 14

theorem record009_parameters : Parameters record009 (rowOfCode 29) 10909772709888 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10909772709888 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch145.candidate14567 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10909772709888
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.small_allowed record009 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch145.candidate14567_checked

theorem record009_result : Result (29, 10909772709888) :=
  of_direct_small 29 10909772709888 (by decide) ⟨record009, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00058.record009.direct_core, record009_parameters, record009_coverage⟩

theorem record010_parameters : Parameters record010 (rowOfCode 29) 10909776871424 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record010_coverage : Coverage record010 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10909776871424 :=
  GraphCoverageDescriptions.coverage_of_checked record010 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11104 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10909776871424
    (by rfl) record010_cells_exact
    (GraphCoverageDescriptions.small_allowed record010 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch111.candidate11104_checked

theorem record010_result : Result (29, 10909776871424) :=
  of_direct_small 29 10909776871424 (by decide) ⟨record010, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00058.record010.direct_core, record010_parameters, record010_coverage⟩

certified_graph_case record011 29 10909888315392 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11105 14

certified_graph_case record012 29 10913512063232 GraphCoverageDescriptions.GraphCoverageBatch145.candidate14568 14

certified_graph_case record013 29 10914317206016 GraphCoverageDescriptions.GraphCoverageBatch145.candidate14569 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00058

module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00091Checked
public import GraphInputsRow31Part00091Metadata
public import GraphInputsRow31Part00091Frames
public import GraphInputsRow31Part00091Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch163
public import GraphInputsRow31Part00091Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00091
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 31) 17783995777024 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 17783995777024 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16375 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 17783995777024
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch163.candidate16375_checked

theorem record000_result : Result (31, 17783995777024) :=
  of_direct_small 31 17783995777024 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00091.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 31 17784119509248 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16376 14

certified_graph_case record002 31 17786265944320 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16377 14

certified_graph_case record003 31 17818288406528 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16378 14

certified_graph_case record004 31 17921558462592 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16379 14

certified_graph_case record005 31 17923704897664 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16380 14

certified_graph_case record006 31 17927999864896 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16381 14

certified_graph_case record007 31 18143075451008 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16382 14

theorem record008_parameters : Parameters record008 (rowOfCode 31) 18152188551232 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 18152188551232 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16383 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 18152188551232
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch163.candidate16383_checked

theorem record008_result : Result (31, 18152188551232) :=
  of_direct_small 31 18152188551232 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00091.record008.direct_core, record008_parameters, record008_coverage⟩

certified_graph_case record009 31 18216836432128 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16384 14

theorem record010_parameters : Parameters record010 (rowOfCode 31) 18252273090560 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record010_coverage : Coverage record010 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 18252273090560 :=
  GraphCoverageDescriptions.coverage_of_checked record010 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16385 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 18252273090560
    (by rfl) record010_cells_exact
    (GraphCoverageDescriptions.small_allowed record010 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch163.candidate16385_checked

theorem record010_result : Result (31, 18252273090560) :=
  of_direct_small 31 18252273090560 (by decide) ⟨record010, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00091.record010.direct_core, record010_parameters, record010_coverage⟩

theorem record011_parameters : Parameters record011 (rowOfCode 31) 18252281413632 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record011_coverage : Coverage record011 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 18252281413632 :=
  GraphCoverageDescriptions.coverage_of_checked record011 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16386 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 18252281413632
    (by rfl) record011_cells_exact
    (GraphCoverageDescriptions.small_allowed record011 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch163.candidate16386_checked

theorem record011_result : Result (31, 18252281413632) :=
  of_direct_small 31 18252281413632 (by decide) ⟨record011, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00091.record011.direct_core, record011_parameters, record011_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00091

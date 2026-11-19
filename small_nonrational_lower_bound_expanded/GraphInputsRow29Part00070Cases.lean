module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00070Checked
public import GraphInputsRow29Part00070Metadata
public import GraphInputsRow29Part00070Frames
public import GraphInputsRow29Part00070Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch112
public import GraphCoverageBatch146
public import GraphInputsRow29Part00070Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00070
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 12320784777856 GraphCoverageDescriptions.GraphCoverageBatch112.candidate11204 14

theorem record001_parameters : Parameters record001 (rowOfCode 29) 12376351473920 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 12376351473920 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch146.candidate14619 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 12376351473920
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch146.candidate14619_checked

theorem record001_result : Result (29, 12376351473920) :=
  of_direct_small 29 12376351473920 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00070.record001.direct_core, record001_parameters, record001_coverage⟩

theorem record002_parameters : Parameters record002 (rowOfCode 29) 12376363503616 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 12376363503616 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch112.candidate11205 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 12376363503616
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch112.candidate11205_checked

theorem record002_result : Result (29, 12376363503616) :=
  of_direct_small 29 12376363503616 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00070.record002.direct_core, record002_parameters, record002_coverage⟩

certified_graph_case record003 29 12376619909248 GraphCoverageDescriptions.GraphCoverageBatch112.candidate11206 14

certified_graph_case record004 29 12376754110592 GraphCoverageDescriptions.GraphCoverageBatch146.candidate14620 14

theorem record005_parameters : Parameters record005 (rowOfCode 29) 12380656373760 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 12380656373760 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch112.candidate11207 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 12380656373760
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch112.candidate11207_checked

theorem record005_result : Result (29, 12380656373760) :=
  of_direct_small 29 12380656373760 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00070.record005.direct_core, record005_parameters, record005_coverage⟩

certified_graph_case record006 29 12380914860160 GraphCoverageDescriptions.GraphCoverageBatch112.candidate11208 14

certified_graph_case record007 29 12382802808832 GraphCoverageDescriptions.GraphCoverageBatch112.candidate11209 14

certified_graph_case record008 29 12382995234944 GraphCoverageDescriptions.GraphCoverageBatch146.candidate14621 14

certified_graph_case record009 29 12387962880128 GraphCoverageDescriptions.GraphCoverageBatch146.candidate14622 14

theorem record010_parameters : Parameters record010 (rowOfCode 29) 12387967074304 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record010_coverage : Coverage record010 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 12387967074304 :=
  GraphCoverageDescriptions.coverage_of_checked record010 GraphCoverageDescriptions.GraphCoverageBatch146.candidate14623 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 12387967074304
    (by rfl) record010_cells_exact
    (GraphCoverageDescriptions.small_allowed record010 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch146.candidate14623_checked

theorem record010_result : Result (29, 12387967074304) :=
  of_direct_small 29 12387967074304 (by decide) ⟨record010, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00070.record010.direct_core, record010_parameters, record010_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00070

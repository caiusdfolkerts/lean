module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00124Checked
public import GraphInputsRow29Part00124Metadata
public import GraphInputsRow29Part00124Frames
public import GraphInputsRow29Part00124Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch116
public import GraphCoverageBatch149
public import GraphInputsRow29Part00124Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00124
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 29) 21007368716288 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 21007368716288 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11635 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 21007368716288
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch116.candidate11635_checked

theorem record000_result : Result (29, 21007368716288) :=
  of_direct_small 29 21007368716288 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00124.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 29 21015946068608 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11636 14

theorem record002_parameters : Parameters record002 (rowOfCode 29) 21076077772800 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 21076077772800 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14988 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 21076077772800
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch149.candidate14988_checked

theorem record002_result : Result (29, 21076077772800) :=
  of_direct_small 29 21076077772800 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00124.record002.direct_core, record002_parameters, record002_coverage⟩

theorem record003_parameters : Parameters record003 (rowOfCode 29) 21076086095872 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 21076086095872 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11637 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 21076086095872
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch116.candidate11637_checked

theorem record003_result : Result (29, 21076086095872) :=
  of_direct_small 29 21076086095872 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00124.record003.direct_core, record003_parameters, record003_coverage⟩

certified_graph_case record004 29 21118423433472 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14989 14

certified_graph_case record005 29 21119160565760 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11638 14

certified_graph_case record006 29 21257072410624 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11639 14

certified_graph_case record007 29 21350955614208 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11640 14

theorem record008_parameters : Parameters record008 (rowOfCode 29) 21367598612480 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 21367598612480 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11641 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 21367598612480
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch116.candidate11641_checked

theorem record008_result : Result (29, 21367598612480) :=
  of_direct_small 29 21367598612480 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00124.record008.direct_core, record008_parameters, record008_coverage⟩

certified_graph_case record009 29 21374041096448 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11642 14

certified_graph_case record010 29 21378338193408 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11643 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00124

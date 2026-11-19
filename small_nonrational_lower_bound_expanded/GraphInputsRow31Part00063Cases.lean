module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00063Checked
public import GraphInputsRow31Part00063Metadata
public import GraphInputsRow31Part00063Frames
public import GraphInputsRow31Part00063Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch160
public import GraphCoverageBatch161
public import GraphInputsRow31Part00063Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00063
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 12850563186944 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16096 14

certified_graph_case record001 31 12876312150016 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16097 14

certified_graph_case record002 31 12920473813248 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16098 14

certified_graph_case record003 31 12932184342528 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16099 14

certified_graph_case record004 31 12932952358912 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16100 14

theorem record005_parameters : Parameters record005 (rowOfCode 31) 12937653682176 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 12937653682176 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16101 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 12937653682176
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch161.candidate16101_checked

theorem record005_result : Result (31, 12937653682176) :=
  of_direct_small 31 12937653682176 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00063.record005.direct_core, record005_parameters, record005_coverage⟩

certified_graph_case record006 31 12937922084864 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16102 14

theorem record007_parameters : Parameters record007 (rowOfCode 31) 12940774244352 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 12940774244352 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16103 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 12940774244352
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch161.candidate16103_checked

theorem record007_result : Result (31, 12940774244352) :=
  of_direct_small 31 12940774244352 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00063.record007.direct_core, record007_parameters, record007_coverage⟩

certified_graph_case record008 31 12945067114496 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16104 14

theorem record009_parameters : Parameters record009 (rowOfCode 31) 12988002107648 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 12988002107648 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16105 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 12988002107648
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.small_allowed record009 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch161.candidate16105_checked

theorem record009_result : Result (31, 12988002107648) :=
  of_direct_small 31 12988002107648 (by decide) ⟨record009, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00063.record009.direct_core, record009_parameters, record009_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00063

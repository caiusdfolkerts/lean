module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00105Checked
public import GraphInputsRow29Part00105Metadata
public import GraphInputsRow29Part00105Frames
public import GraphInputsRow29Part00105Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch115
public import GraphCoverageBatch148
public import GraphInputsRow29Part00105Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00105
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 18151917043968 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14818 14

certified_graph_case record001 29 18181884248320 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14819 14

certified_graph_case record002 29 18181884313600 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11539 14

certified_graph_case record003 29 18182012207360 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14820 14

certified_graph_case record004 29 18182016434176 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14821 14

certified_graph_case record005 29 18186177118464 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14822 14

certified_graph_case record006 29 18220939510016 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14823 14

certified_graph_case record007 29 18229529444480 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14824 14

certified_graph_case record008 29 18229598625920 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14825 14

certified_graph_case record009 29 18248649212160 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14826 14

certified_graph_case record010 29 18248657600512 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11540 14

certified_graph_case record011 29 18249049735424 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14827 14

certified_graph_case record012 29 18252809961728 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14828 14

certified_graph_case record013 29 18253346832384 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14829 14

certified_graph_case record014 29 18253355155456 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11541 14

theorem record015_parameters : Parameters record015 (rowOfCode 29) 18255030845440 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record015_coverage : Coverage record015 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 18255030845440 :=
  GraphCoverageDescriptions.coverage_of_checked record015 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14830 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 18255030845440
    (by rfl) record015_cells_exact
    (GraphCoverageDescriptions.small_allowed record015 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch148.candidate14830_checked

theorem record015_result : Result (29, 18255030845440) :=
  of_direct_small 29 18255030845440 (by decide) ⟨record015, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00105.record015.direct_core, record015_parameters, record015_coverage⟩

certified_graph_case record016 29 18255290859776 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14831 14

certified_graph_case record017 29 18257507581952 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14832 14

certified_graph_case record018 29 18262765109376 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14833 14

certified_graph_case record019 29 18265023742208 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14834 14

certified_graph_case record020 29 18265032130560 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14835 14

certified_graph_case record021 29 18271933858048 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11542 14

theorem record022_parameters : Parameters record022 (rowOfCode 29) 18272070205440 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record022_coverage : Coverage record022 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 18272070205440 :=
  GraphCoverageDescriptions.coverage_of_checked record022 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11543 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 18272070205440
    (by rfl) record022_cells_exact
    (GraphCoverageDescriptions.small_allowed record022 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch115.candidate11543_checked

theorem record022_result : Result (29, 18272070205440) :=
  of_direct_small 29 18272070205440 (by decide) ⟨record022, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00105.record022.direct_core, record022_parameters, record022_coverage⟩

certified_graph_case record023 29 18272078528512 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11544 14

certified_graph_case record024 29 18288533381184 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14836 14

certified_graph_case record025 29 18289390584064 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14837 14

certified_graph_case record026 29 18289589952576 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14838 14

certified_graph_case record027 29 18289658986752 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14839 14

certified_graph_case record028 29 18289659052032 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14840 14

certified_graph_case record029 29 18289661067520 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14841 14

certified_graph_case record030 29 18297838928128 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14842 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00105

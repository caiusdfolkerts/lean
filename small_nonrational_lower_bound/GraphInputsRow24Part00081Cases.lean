module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00081Checked
public import GraphInputsRow24Part00081Metadata
public import GraphInputsRow24Part00081Frames
public import GraphInputsRow24Part00081Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch089
public import GraphInputsRow24Part00081Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 24438978381824 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08970 14

certified_graph_case record001 24 24441182487296 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08971 14

certified_graph_case record002 24 24443262862080 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08972 14

certified_graph_case record003 24 24447155470592 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08973 14

certified_graph_case record004 24 24447167760384 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08974 14

certified_graph_case record005 24 24447289671936 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08975 14

certified_graph_case record006 24 24447299880960 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08976 14

theorem record007_parameters : Parameters record007 (rowOfCode 24) 24447365941248 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24447365941248 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08977 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24447365941248
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch089.candidate08977_checked

theorem record007_result : Result (24, 24447365941248) :=
  of_direct_small 24 24447365941248 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00081.record007.direct_core, record007_parameters, record007_coverage⟩
#print axioms record007_result

certified_graph_case record008 24 24447512756224 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08978 14

certified_graph_case record009 24 24447759425600 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08979 14

certified_graph_case record010 24 24449906639424 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08980 14

theorem record011_parameters : Parameters record011 (rowOfCode 24) 24457691414784 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record011_coverage : Coverage record011 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24457691414784 :=
  GraphCoverageDescriptions.coverage_of_checked record011 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08981 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24457691414784
    (by rfl) record011_cells_exact
    (GraphCoverageDescriptions.small_allowed record011 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch089.candidate08981_checked

theorem record011_result : Result (24, 24457691414784) :=
  of_direct_small 24 24457691414784 (by decide) ⟨record011, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00081.record011.direct_core, record011_parameters, record011_coverage⟩
#print axioms record011_result

certified_graph_case record012 24 24457825681408 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08982 14

certified_graph_case record013 24 24457834004480 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08983 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00081

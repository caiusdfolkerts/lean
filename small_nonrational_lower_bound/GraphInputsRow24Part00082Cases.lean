module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00082Checked
public import GraphInputsRow24Part00082Metadata
public import GraphInputsRow24Part00082Frames
public import GraphInputsRow24Part00082Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch089
public import GraphInputsRow24Part00082Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 24) 24458228285440 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24458228285440 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08984 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24458228285440
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch089.candidate08984_checked

theorem record000_result : Result (24, 24458228285440) :=
  of_direct_small 24 24458228285440 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00082.record000.direct_core, record000_parameters, record000_coverage⟩
#print axioms record000_result

theorem record001_parameters : Parameters record001 (rowOfCode 24) 24458362356224 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24458362356224 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08985 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24458362356224
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch089.candidate08985_checked

theorem record001_result : Result (24, 24458362356224) :=
  of_direct_small 24 24458362356224 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00082.record001.direct_core, record001_parameters, record001_coverage⟩
#print axioms record001_result

certified_graph_case record002 24 24467525894400 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08986 14

certified_graph_case record003 24 24470918009088 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08987 14

certified_graph_case record004 24 24471761092608 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08988 14

certified_graph_case record005 24 24471827152896 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08989 14

theorem record006_parameters : Parameters record006 (rowOfCode 24) 24484705763328 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24484705763328 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08990 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24484705763328
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch089.candidate08990_checked

theorem record006_result : Result (24, 24484705763328) :=
  of_direct_small 24 24484705763328 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00082.record006.direct_core, record006_parameters, record006_coverage⟩
#print axioms record006_result

certified_graph_case record007 24 24499721371904 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08991 14

certified_graph_case record008 24 24499779012736 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08992 14

certified_graph_case record009 24 24502123692032 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08993 14

certified_graph_case record010 24 24504204066816 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08994 14

certified_graph_case record011 24 24508494790912 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08995 14

certified_graph_case record012 24 24508560851200 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08996 14

certified_graph_case record013 24 24512789807104 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08997 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00082

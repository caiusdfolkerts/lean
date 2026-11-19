module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00003Checked
public import GraphInputsRow29Part00003Metadata
public import GraphInputsRow29Part00003Frames
public import GraphInputsRow29Part00003Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch105
public import GraphCoverageBatch143
public import GraphInputsRow29Part00003Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00003
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 29) 1042135679232 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 1042135679232 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10537 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 1042135679232
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch105.candidate10537_checked

theorem record000_result : Result (29, 1042135679232) :=
  of_direct_small 29 1042135679232 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00003.record000.direct_core, record000_parameters, record000_coverage⟩
#print axioms record000_result

certified_graph_case record001 29 1174210183424 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10538 14

certified_graph_case record002 29 1174283583520 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10539 14

certified_graph_case record003 29 1209716998400 GraphCoverageDescriptions.GraphCoverageBatch143.candidate14313 14

certified_graph_case record004 29 1214009868544 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10540 14

certified_graph_case record005 29 1222331367680 GraphCoverageDescriptions.GraphCoverageBatch143.candidate14314 14

certified_graph_case record006 29 1255818756160 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10541 14

certified_graph_case record007 29 1323413110848 GraphCoverageDescriptions.GraphCoverageBatch143.candidate14315 14

certified_graph_case record008 29 1347147596032 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10542 14

certified_graph_case record009 29 1364327464960 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10543 14

certified_graph_case record010 29 1422317944832 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10544 14

certified_graph_case record011 29 1422452080896 GraphCoverageDescriptions.GraphCoverageBatch143.candidate14316 14

certified_graph_case record012 29 1469696712768 GraphCoverageDescriptions.GraphCoverageBatch143.candidate14317 14

certified_graph_case record013 29 1484318114048 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10545 14

theorem record014_parameters : Parameters record014 (rowOfCode 29) 1507739107328 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record014_coverage : Coverage record014 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 1507739107328 :=
  GraphCoverageDescriptions.coverage_of_checked record014 GraphCoverageDescriptions.GraphCoverageBatch105.candidate10546 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 1507739107328
    (by rfl) record014_cells_exact
    (GraphCoverageDescriptions.small_allowed record014 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch105.candidate10546_checked

theorem record014_result : Result (29, 1507739107328) :=
  of_direct_small 29 1507739107328 (by decide) ⟨record014, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00003.record014.direct_core, record014_parameters, record014_coverage⟩
#print axioms record014_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00003

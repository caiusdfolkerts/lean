module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00032Checked
public import GraphInputsRow29Part00032Metadata
public import GraphInputsRow29Part00032Frames
public import GraphInputsRow29Part00032Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch108
public import GraphCoverageBatch144
public import GraphInputsRow29Part00032Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 7003883700224 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10869 14

certified_graph_case record001 29 7048242954496 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10870 14

certified_graph_case record002 29 7050864164864 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10871 14

certified_graph_case record003 29 7080339603712 GraphCoverageDescriptions.GraphCoverageBatch144.candidate14425 14

certified_graph_case record004 29 7098039566336 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10872 14

certified_graph_case record005 29 7150227194112 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10873 14

certified_graph_case record006 29 7150227259392 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10874 14

certified_graph_case record007 29 7150355153152 GraphCoverageDescriptions.GraphCoverageBatch144.candidate14426 14

certified_graph_case record008 29 7150359314688 GraphCoverageDescriptions.GraphCoverageBatch144.candidate14427 14

certified_graph_case record009 29 7150359379968 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10875 14

theorem record010_parameters : Parameters record010 (rowOfCode 29) 7150462046464 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record010_coverage : Coverage record010 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 7150462046464 :=
  GraphCoverageDescriptions.coverage_of_checked record010 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10876 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 7150462046464
    (by rfl) record010_cells_exact
    (GraphCoverageDescriptions.small_allowed record010 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch108.candidate10876_checked

theorem record010_result : Result (29, 7150462046464) :=
  of_direct_small 29 7150462046464 (by decide) ⟨record010, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00032.record010.direct_core, record010_parameters, record010_coverage⟩
#print axioms record010_result

certified_graph_case record011 29 7154085924880 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10877 14

certified_graph_case record012 29 7156703170816 GraphCoverageDescriptions.GraphCoverageBatch144.candidate14428 14

certified_graph_case record013 29 7156794458368 GraphCoverageDescriptions.GraphCoverageBatch144.candidate14429 14

certified_graph_case record014 29 7156800765952 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10878 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032

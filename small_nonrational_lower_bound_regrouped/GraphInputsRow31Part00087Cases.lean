module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00087Checked
public import GraphInputsRow31Part00087Metadata
public import GraphInputsRow31Part00087Frames
public import GraphInputsRow31Part00087Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch163
public import GraphInputsRow31Part00087Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00087
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 17630180245504 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16340 14

certified_graph_case record001 31 17630182260992 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16341 14

certified_graph_case record002 31 17630584913984 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16342 14

certified_graph_case record003 31 17632128499712 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16343 14

certified_graph_case record004 31 17632260620288 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16344 14

certified_graph_case record005 31 17632262635776 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16345 14

theorem record006_parameters : Parameters record006 (rowOfCode 31) 17632732389440 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 17632732389440 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16346 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 17632732389440
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch163.candidate16346_checked

theorem record006_result : Result (31, 17632732389440) :=
  of_direct_small 31 17632732389440 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00087.record006.direct_core, record006_parameters, record006_coverage⟩
#print axioms record006_result

certified_graph_case record007 31 17636555505920 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16347 14

certified_graph_case record008 31 17636555571200 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16348 14

certified_graph_case record009 31 17636819747072 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16349 14

certified_graph_case record010 31 17636819812352 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16350 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00087

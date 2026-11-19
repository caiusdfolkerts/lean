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

theorem record004_parameters : Parameters record004 (rowOfCode 31) 17632260620288 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 17632260620288 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16344 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 17632260620288
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch163.candidate16344_checked

theorem record004_result : Result (31, 17632260620288) :=
  of_direct_small 31 17632260620288 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00087.record004.direct_core, record004_parameters, record004_coverage⟩

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

certified_graph_case record007 31 17636555505920 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16347 14

certified_graph_case record008 31 17636555571200 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16348 14

certified_graph_case record009 31 17636819747072 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16349 14

theorem record010_parameters : Parameters record010 (rowOfCode 31) 17636819812352 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record010_coverage : Coverage record010 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 17636819812352 :=
  GraphCoverageDescriptions.coverage_of_checked record010 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16350 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 17636819812352
    (by rfl) record010_cells_exact
    (GraphCoverageDescriptions.small_allowed record010 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch163.candidate16350_checked

theorem record010_result : Result (31, 17636819812352) :=
  of_direct_small 31 17636819812352 (by decide) ⟨record010, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00087.record010.direct_core, record010_parameters, record010_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00087

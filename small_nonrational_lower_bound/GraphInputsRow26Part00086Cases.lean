module
prelude
public meta import GraphCases
public import GraphInputsRow26Part00086Checked
public import GraphInputsRow26Part00086Metadata
public import GraphInputsRow26Part00086Frames
public import GraphInputsRow26Part00086Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch104
public import GraphCoverageBatch130
public import GraphInputsRow26Part00086Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00086
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 26 34746856112128 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10467 14

certified_graph_case record001 26 34747359363072 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10468 14

certified_graph_case record002 26 34763465294340 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10469 14

theorem record003_parameters : Parameters record003 (rowOfCode 26) 34763465428992 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34763465428992 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10470 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 34763465428992
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch104.candidate10470_checked

theorem record003_result : Result (26, 34763465428992) :=
  of_direct_small 26 34763465428992 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00086.record003.direct_core, record003_parameters, record003_coverage⟩
#print axioms record003_result

certified_graph_case record004 26 34763482595328 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10471 14

certified_graph_case record005 26 34763515625472 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10472 14

certified_graph_case record006 26 34764539166720 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10473 14

certified_graph_case record007 26 34875134576896 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10474 14

certified_graph_case record008 26 34875151548416 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10475 14

theorem record009_parameters : Parameters record009 (rowOfCode 26) 34875688353792 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34875688353792 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10476 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 34875688353792
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.small_allowed record009 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch104.candidate10476_checked

theorem record009_result : Result (26, 34875688353792) :=
  of_direct_small 26 34875688353792 (by decide) ⟨record009, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00086.record009.direct_core, record009_parameters, record009_coverage⟩
#print axioms record009_result

theorem record010_parameters : Parameters record010 (rowOfCode 26) 34892314445824 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record010_coverage : Coverage record010 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34892314445824 :=
  GraphCoverageDescriptions.coverage_of_checked record010 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10477 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 34892314445824
    (by rfl) record010_cells_exact
    (GraphCoverageDescriptions.small_allowed record010 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch104.candidate10477_checked

theorem record010_result : Result (26, 34892314445824) :=
  of_direct_small 26 34892314445824 (by decide) ⟨record010, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00086.record010.direct_core, record010_parameters, record010_coverage⟩
#print axioms record010_result

certified_graph_case record011 26 35115652745224 GraphCoverageDescriptions.GraphCoverageBatch130.candidate13096 14

certified_graph_case record012 26 35115669522432 GraphCoverageDescriptions.GraphCoverageBatch130.candidate13097 14

certified_graph_case record013 26 35115669782528 GraphCoverageDescriptions.GraphCoverageBatch130.candidate13098 14

certified_graph_case record014 26 35150012483584 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10478 14

certified_graph_case record015 26 35150029389824 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10479 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00086

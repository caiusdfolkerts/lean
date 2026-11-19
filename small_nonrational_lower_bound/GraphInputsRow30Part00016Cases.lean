module
prelude
public meta import GraphCases
public import GraphInputsRow30Part00016Checked
public import GraphInputsRow30Part00016Metadata
public import GraphInputsRow30Part00016Frames
public import GraphInputsRow30Part00016Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch109
public import GraphCoverageBatch110
public import GraphCoverageBatch155
public import GraphInputsRow30Part00016Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 30 8247973560320 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10992 14

certified_graph_case record001 30 8250926305536 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10993 14

certified_graph_case record002 30 8250926370816 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10994 14

certified_graph_case record003 30 8251190546688 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10995 14

certified_graph_case record004 30 8251190611968 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10996 14

theorem record005_parameters : Parameters record005 (rowOfCode 30) 8251198410768 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8251198410768 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10997 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8251198410768
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch109.candidate10997_checked

theorem record005_result : Result (30, 8251198410768) :=
  of_direct_small 30 8251198410768 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00016.record005.direct_core, record005_parameters, record005_coverage⟩
#print axioms record005_result

certified_graph_case record006 30 8251215185936 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10998 14

certified_graph_case record007 30 8252288925697 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10999 14

certified_graph_case record008 30 8263697434640 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11000 14

certified_graph_case record009 30 8264073383936 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11001 14

certified_graph_case record010 30 8264077021200 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15551 14

theorem record011_parameters : Parameters record011 (rowOfCode 30) 8264093796368 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record011_coverage : Coverage record011 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8264093796368 :=
  GraphCoverageDescriptions.coverage_of_checked record011 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8264093796368
    (by rfl) record011_cells_exact
    (GraphCoverageDescriptions.small_allowed record011 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch110.candidate11002_checked

theorem record011_result : Result (30, 8264093796368) :=
  of_direct_small 30 8264093796368 (by decide) ⟨record011, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00016.record011.direct_core, record011_parameters, record011_coverage⟩
#print axioms record011_result

theorem record012_parameters : Parameters record012 (rowOfCode 30) 8265167536129 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record012_coverage : Coverage record012 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8265167536129 :=
  GraphCoverageDescriptions.coverage_of_checked record012 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8265167536129
    (by rfl) record012_cells_exact
    (GraphCoverageDescriptions.small_allowed record012 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch110.candidate11003_checked

theorem record012_result : Result (30, 8265167536129) :=
  of_direct_small 30 8265167536129 (by decide) ⟨record012, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00016.record012.direct_core, record012_parameters, record012_coverage⟩
#print axioms record012_result

certified_graph_case record013 30 8265171763200 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11004 14

certified_graph_case record014 30 8315350552832 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11005 14

certified_graph_case record015 30 8324192012304 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11006 14

certified_graph_case record016 30 8324209180673 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11007 14

certified_graph_case record017 30 8324209246208 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11008 14

certified_graph_case record018 30 8325265752065 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11009 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00016

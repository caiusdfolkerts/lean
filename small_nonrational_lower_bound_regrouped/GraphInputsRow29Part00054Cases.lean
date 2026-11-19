module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00054Checked
public import GraphInputsRow29Part00054Metadata
public import GraphInputsRow29Part00054Frames
public import GraphInputsRow29Part00054Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch110
public import GraphInputsRow29Part00054Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00054
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 29) 10448996929792 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10448996929792 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11077 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10448996929792
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch110.candidate11077_checked

theorem record000_result : Result (29, 10448996929792) :=
  of_direct_small 29 10448996929792 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00054.record000.direct_core, record000_parameters, record000_coverage⟩
#print axioms record000_result

certified_graph_case record001 29 10455599890432 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11078 14

theorem record002_parameters : Parameters record002 (rowOfCode 29) 10456781557776 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10456781557776 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11079 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10456781557776
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch110.candidate11079_checked

theorem record002_result : Result (29, 10456781557776) :=
  of_direct_small 29 10456781557776 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00054.record002.direct_core, record002_parameters, record002_coverage⟩
#print axioms record002_result

certified_graph_case record003 29 10484309393408 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11080 14

certified_graph_case record004 29 10484312969472 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11081 14

certified_graph_case record005 29 10488604344320 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11082 14

certified_graph_case record006 29 10488605839616 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11083 14

certified_graph_case record007 29 10488868585472 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11084 14

certified_graph_case record008 29 10488870080768 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11085 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00054

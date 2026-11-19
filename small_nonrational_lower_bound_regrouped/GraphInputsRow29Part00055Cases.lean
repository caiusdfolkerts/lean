module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00055Checked
public import GraphInputsRow29Part00055Metadata
public import GraphInputsRow29Part00055Frames
public import GraphInputsRow29Part00055Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch110
public import GraphCoverageBatch145
public import GraphInputsRow29Part00055Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 29) 10488993810448 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10488993810448 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11086 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10488993810448
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch110.candidate11086_checked

theorem record000_result : Result (29, 10488993810448) :=
  of_direct_small 29 10488993810448 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00055.record000.direct_core, record000_parameters, record000_coverage⟩
#print axioms record000_result

theorem record001_parameters : Parameters record001 (rowOfCode 29) 10490067550209 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10490067550209 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11087 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10490067550209
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch110.candidate11087_checked

theorem record001_result : Result (29, 10490067550209) :=
  of_direct_small 29 10490067550209 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00055.record001.direct_core, record001_parameters, record001_coverage⟩
#print axioms record001_result

certified_graph_case record002 29 10498781249792 GraphCoverageDescriptions.GraphCoverageBatch145.candidate14555 14

certified_graph_case record003 29 10585242603776 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11088 14

certified_graph_case record004 29 10585506844928 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11089 14

certified_graph_case record005 29 10601399058433 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11090 14

certified_graph_case record006 29 10639451881472 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11091 14

certified_graph_case record007 29 10643736428544 GraphCoverageDescriptions.GraphCoverageBatch145.candidate14556 14

certified_graph_case record008 29 10678094004992 GraphCoverageDescriptions.GraphCoverageBatch145.candidate14557 14

certified_graph_case record009 29 10722677362944 GraphCoverageDescriptions.GraphCoverageBatch145.candidate14558 14

certified_graph_case record010 29 10740371570816 GraphCoverageDescriptions.GraphCoverageBatch145.candidate14559 14

certified_graph_case record011 29 10781580132352 GraphCoverageDescriptions.GraphCoverageBatch145.candidate14560 14

certified_graph_case record012 29 10781852696576 GraphCoverageDescriptions.GraphCoverageBatch110.candidate11092 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00055

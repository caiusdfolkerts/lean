module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00143Checked
public import GraphInputsRow24Part00143Metadata
public import GraphInputsRow24Part00143Frames
public import GraphInputsRow24Part00143Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch101
public import GraphInputsRow24Part00143Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00143
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 32059313897728 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10156 14

certified_graph_case record001 24 32074916708608 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10157 14

theorem record002_parameters : Parameters record002 (rowOfCode 24) 32075371003904 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32075371003904 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10158 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 32075371003904
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch101.candidate10158_checked

theorem record002_result : Result (24, 32075371003904) :=
  of_direct_small 24 32075371003904 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00143.record002.direct_core, record002_parameters, record002_coverage⟩
#print axioms record002_result

certified_graph_case record003 24 32076493488704 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10159 14

certified_graph_case record004 24 32076512362496 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10160 14

certified_graph_case record005 24 32078037139712 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10161 14

certified_graph_case record006 24 32078171406336 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10162 14

certified_graph_case record007 24 32078179729408 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10163 14

theorem record008_parameters : Parameters record008 (rowOfCode 24) 32078574010368 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32078574010368 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10164 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 32078574010368
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch101.candidate10164_checked

theorem record008_result : Result (24, 32078574010368) :=
  of_direct_small 24 32078574010368 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00143.record008.direct_core, record008_parameters, record008_coverage⟩
#print axioms record008_result

certified_graph_case record009 24 32078708081152 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10165 14

certified_graph_case record010 24 32163157250112 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10166 14

certified_graph_case record011 24 32163421491264 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10167 14

certified_graph_case record012 24 32164039131392 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10168 14

certified_graph_case record013 24 32164049600512 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10169 14

certified_graph_case record014 24 32164247781376 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10170 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00143

module
prelude
public meta import GraphCases
public import GraphInputsRow26Part00071Checked
public import GraphInputsRow26Part00071Metadata
public import GraphInputsRow26Part00071Frames
public import GraphInputsRow26Part00071Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch101
public import GraphInputsRow26Part00071Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 26 32012271353856 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10147 14

certified_graph_case record001 26 32012337414144 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10148 14

certified_graph_case record002 26 32025986732096 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10149 14

certified_graph_case record003 26 32026600210688 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10150 14

theorem record004_parameters : Parameters record004 (rowOfCode 26) 32027077263360 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32027077263360 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10151 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 32027077263360
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch101.candidate10151_checked

theorem record004_result : Result (26, 32027077263360) :=
  of_direct_small 26 32027077263360 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00071.record004.direct_core, record004_parameters, record004_coverage⟩

certified_graph_case record005 26 32043780079616 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10152 14

certified_graph_case record006 26 32044316884992 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10153 14

certified_graph_case record007 26 32059272740864 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10155 14

certified_graph_case record008 26 32075371003904 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10158 14

certified_graph_case record009 26 32076493488704 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10159 14

certified_graph_case record010 26 32076512362496 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10160 14

certified_graph_case record011 26 32078179729408 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10163 14

certified_graph_case record012 26 32078574010368 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10164 14

certified_graph_case record013 26 32163157250112 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10166 14

certified_graph_case record014 26 32163421491264 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10167 14

certified_graph_case record015 26 32164039131392 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10168 14

certified_graph_case record016 26 32164049600512 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10169 14

certified_graph_case record017 26 32164247781376 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10170 14

certified_graph_case record018 26 32172629098496 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10173 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00071

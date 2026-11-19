module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00078Checked
public import GraphInputsRow31Part00078Metadata
public import GraphInputsRow31Part00078Frames
public import GraphInputsRow31Part00078Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch162
public import GraphInputsRow31Part00078Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00078
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 14587392950272 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16211 14

certified_graph_case record001 31 14587454849024 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16212 14

certified_graph_case record002 31 14590809743360 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16213 14

certified_graph_case record003 31 14606248509440 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16214 14

certified_graph_case record004 31 14616587403264 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16215 14

certified_graph_case record005 31 14622354636800 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16216 14

certified_graph_case record006 31 14624363806976 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16217 14

certified_graph_case record007 31 14625168949760 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16218 14

certified_graph_case record008 31 14628797087744 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16219 14

certified_graph_case record009 31 14629466013696 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16220 14

certified_graph_case record010 31 14663018488064 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16221 14

certified_graph_case record011 31 14663089717248 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16222 14

certified_graph_case record012 31 14663824703488 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16223 14

certified_graph_case record013 31 15213050986496 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16224 14

certified_graph_case record014 31 15213579468800 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16225 14

theorem record015_parameters : Parameters record015 (rowOfCode 31) 15403138949120 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record015_coverage : Coverage record015 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 15403138949120 :=
  GraphCoverageDescriptions.coverage_of_checked record015 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16226 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 15403138949120
    (by rfl) record015_cells_exact
    (GraphCoverageDescriptions.small_allowed record015 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch162.candidate16226_checked

theorem record015_result : Result (31, 15403138949120) :=
  of_direct_small 31 15403138949120 (by decide) ⟨record015, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00078.record015.direct_core, record015_parameters, record015_coverage⟩

certified_graph_case record016 31 15472352362496 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16227 14

certified_graph_case record017 31 15480207212800 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16228 14

certified_graph_case record018 31 15480942264320 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16229 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00078

module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00080Checked
public import GraphInputsRow31Part00080Metadata
public import GraphInputsRow31Part00080Frames
public import GraphInputsRow31Part00080Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch162
public import GraphInputsRow31Part00080Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00080
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 15680960233728 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16235 14

certified_graph_case record001 31 15681731436544 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16236 14

certified_graph_case record002 31 15686363545728 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16237 14

theorem record003_parameters : Parameters record003 (rowOfCode 31) 15686698041344 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 15686698041344 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16238 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 15686698041344
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch162.candidate16238_checked

theorem record003_result : Result (31, 15686698041344) :=
  of_direct_small 31 15686698041344 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00080.record003.direct_core, record003_parameters, record003_coverage⟩

certified_graph_case record004 31 15689550168192 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16239 14

certified_graph_case record005 31 15693845119104 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16240 14

theorem record006_parameters : Parameters record006 (rowOfCode 31) 15721866231808 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 15721866231808 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16241 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 15721866231808
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch162.candidate16241_checked

theorem record006_result : Result (31, 15721866231808) :=
  of_direct_small 31 15721866231808 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00080.record006.direct_core, record006_parameters, record006_coverage⟩

certified_graph_case record007 31 15723875434624 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16242 14

certified_graph_case record008 31 15762530115712 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16243 14

certified_graph_case record009 31 15851247894528 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16244 14

certified_graph_case record010 31 15859305152512 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16245 14

certified_graph_case record011 31 16381005267460 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16246 14

certified_graph_case record012 31 16495931326720 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16247 14

certified_graph_case record013 31 16496067674112 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16248 14

certified_graph_case record014 31 16496075997184 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16249 14

certified_graph_case record015 31 16496298885120 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16250 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00080

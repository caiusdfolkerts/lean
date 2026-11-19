module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00102Checked
public import GraphInputsRow24Part00102Metadata
public import GraphInputsRow24Part00102Frames
public import GraphInputsRow24Part00102Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch093
public import GraphInputsRow24Part00102Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 25702244040960 GraphCoverageDescriptions.GraphCoverageBatch093.candidate09327 14

certified_graph_case record001 24 25702252429312 GraphCoverageDescriptions.GraphCoverageBatch093.candidate09328 14

certified_graph_case record002 24 25702310101248 GraphCoverageDescriptions.GraphCoverageBatch093.candidate09329 14

certified_graph_case record003 24 25702312247296 GraphCoverageDescriptions.GraphCoverageBatch093.candidate09330 14

certified_graph_case record004 24 25702318489600 GraphCoverageDescriptions.GraphCoverageBatch093.candidate09331 14

certified_graph_case record005 24 25702359646464 GraphCoverageDescriptions.GraphCoverageBatch093.candidate09332 14

certified_graph_case record006 24 25702369855488 GraphCoverageDescriptions.GraphCoverageBatch093.candidate09333 14

certified_graph_case record007 24 25702712754240 GraphCoverageDescriptions.GraphCoverageBatch093.candidate09334 14

certified_graph_case record008 24 25702714851328 GraphCoverageDescriptions.GraphCoverageBatch093.candidate09335 14

theorem record009_parameters : Parameters record009 (rowOfCode 24) 25702762299456 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25702762299456 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch093.candidate09336 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25702762299456
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.small_allowed record009 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch093.candidate09336_checked

theorem record009_result : Result (24, 25702762299456) :=
  of_direct_small 24 25702762299456 (by decide) ⟨record009, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00102.record009.direct_core, record009_parameters, record009_coverage⟩
#print axioms record009_result

theorem record010_parameters : Parameters record010 (rowOfCode 24) 25702829400128 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record010_coverage : Coverage record010 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25702829400128 :=
  GraphCoverageDescriptions.coverage_of_checked record010 GraphCoverageDescriptions.GraphCoverageBatch093.candidate09337 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25702829400128
    (by rfl) record010_cells_exact
    (GraphCoverageDescriptions.small_allowed record010 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch093.candidate09337_checked

theorem record010_result : Result (24, 25702829400128) :=
  of_direct_small 24 25702829400128 (by decide) ⟨record010, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00102.record010.direct_core, record010_parameters, record010_coverage⟩
#print axioms record010_result

certified_graph_case record011 24 25704976613952 GraphCoverageDescriptions.GraphCoverageBatch093.candidate09338 14

certified_graph_case record012 24 25705480208640 GraphCoverageDescriptions.GraphCoverageBatch093.candidate09339 14

certified_graph_case record013 24 25705490417664 GraphCoverageDescriptions.GraphCoverageBatch093.candidate09340 14

certified_graph_case record014 24 25705531899904 GraphCoverageDescriptions.GraphCoverageBatch093.candidate09341 14

certified_graph_case record015 24 25705556477952 GraphCoverageDescriptions.GraphCoverageBatch093.candidate09342 14

certified_graph_case record016 24 25705933447232 GraphCoverageDescriptions.GraphCoverageBatch093.candidate09343 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00102

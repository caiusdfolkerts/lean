module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00161Checked
public import GraphInputsRow24Part00161Metadata
public import GraphInputsRow24Part00161Frames
public import GraphInputsRow24Part00161Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch103
public import GraphInputsRow24Part00161Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00161
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 33126320455680 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10343 14

certified_graph_case record001 24 33158515933184 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10344 14

certified_graph_case record002 24 33158557090048 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10345 14

certified_graph_case record003 24 33167415181888 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10346 14

certified_graph_case record004 24 33195132256256 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10347 14

certified_graph_case record005 24 33197212631040 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10348 14

certified_graph_case record006 24 33204426776832 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10349 14

certified_graph_case record007 24 33205534130176 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10350 14

theorem record008_parameters : Parameters record008 (rowOfCode 24) 33206070935552 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 33206070935552 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10351 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 33206070935552
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch103.candidate10351_checked

theorem record008_result : Result (24, 33206070935552) :=
  of_direct_small 24 33206070935552 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00161.record008.direct_core, record008_parameters, record008_coverage⟩
#print axioms record008_result

certified_graph_case record009 24 33206574317568 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10352 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00161

module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00157Checked
public import GraphInputsRow24Part00157Metadata
public import GraphInputsRow24Part00157Frames
public import GraphInputsRow24Part00157Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch103
public import GraphInputsRow24Part00157Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00157
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 32788334518272 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10302 14

certified_graph_case record001 24 32788335558656 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10303 14

theorem record002_parameters : Parameters record002 (rowOfCode 24) 32788351033344 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32788351033344 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10304 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 32788351033344
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch103.candidate10304_checked

theorem record002_result : Result (24, 32788351033344) :=
  of_direct_small 24 32788351033344 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00157.record002.direct_core, record002_parameters, record002_coverage⟩
#print axioms record002_result

certified_graph_case record003 24 32788854219008 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10305 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00157

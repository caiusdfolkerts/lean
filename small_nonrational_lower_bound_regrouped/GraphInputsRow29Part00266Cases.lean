module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00266Checked
public import GraphInputsRow29Part00266Metadata
public import GraphInputsRow29Part00266Frames
public import GraphInputsRow29Part00266Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch122
public import GraphCoverageBatch155
public import GraphInputsRow29Part00266Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00266
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 33099576508416 GraphCoverageDescriptions.GraphCoverageBatch122.candidate12254 14

certified_graph_case record001 29 33133122552352 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15531 14

certified_graph_case record002 29 33167417278464 GraphCoverageDescriptions.GraphCoverageBatch122.candidate12255 14

theorem record003_parameters : Parameters record003 (rowOfCode 29) 33204460388352 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 33204460388352 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch122.candidate12256 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 33204460388352
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch122.candidate12256_checked

theorem record003_result : Result (29, 33204460388352) :=
  of_direct_small 29 33204460388352 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00266.record003.direct_core, record003_parameters, record003_coverage⟩
#print axioms record003_result

certified_graph_case record004 29 33238827401216 GraphCoverageDescriptions.GraphCoverageBatch122.candidate12257 14

certified_graph_case record005 29 33260382195744 GraphCoverageDescriptions.GraphCoverageBatch122.candidate12258 14

certified_graph_case record006 29 33262458650752 GraphCoverageDescriptions.GraphCoverageBatch122.candidate12259 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00266

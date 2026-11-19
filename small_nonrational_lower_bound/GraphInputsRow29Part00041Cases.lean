module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00041Checked
public import GraphInputsRow29Part00041Metadata
public import GraphInputsRow29Part00041Frames
public import GraphInputsRow29Part00041Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch109
public import GraphInputsRow29Part00041Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 7593905096960 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10945 14

certified_graph_case record001 29 7597818183936 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10946 14

theorem record002_parameters : Parameters record002 (rowOfCode 29) 7598065715456 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 7598065715456 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10947 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 7598065715456
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch109.candidate10947_checked

theorem record002_result : Result (29, 7598065715456) :=
  of_direct_small 29 7598065715456 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00041.record002.direct_core, record002_parameters, record002_coverage⟩
#print axioms record002_result

certified_graph_case record003 29 7598074103808 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10948 14

theorem record004_parameters : Parameters record004 (rowOfCode 29) 7598082360064 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 7598082360064 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10949 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 7598082360064
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch109.candidate10949_checked

theorem record004_result : Result (29, 7598082360064) :=
  of_direct_small 29 7598082360064 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00041.record004.direct_core, record004_parameters, record004_coverage⟩
#print axioms record004_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00041

module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00223Checked
public import GraphInputsRow29Part00223Metadata
public import GraphInputsRow29Part00223Frames
public import GraphInputsRow29Part00223Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch120
public import GraphCoverageBatch154
public import GraphInputsRow29Part00223Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00223
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 30242743779856 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12053 14

certified_graph_case record001 29 30246537592832 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12054 14

certified_graph_case record002 29 30246636683264 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15452 14

certified_graph_case record003 29 30253917671552 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12055 14

certified_graph_case record004 29 30254152552464 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12056 14

theorem record005_parameters : Parameters record005 (rowOfCode 29) 30255226028560 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 30255226028560 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12057 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 30255226028560
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch120.candidate12057_checked

theorem record005_result : Result (29, 30255226028560) :=
  of_direct_small 29 30255226028560 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00223.record005.direct_core, record005_parameters, record005_coverage⟩
#print axioms record005_result

certified_graph_case record006 29 30305583108096 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12058 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00223

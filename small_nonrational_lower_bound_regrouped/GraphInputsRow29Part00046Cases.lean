module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00046Checked
public import GraphInputsRow29Part00046Metadata
public import GraphInputsRow29Part00046Frames
public import GraphInputsRow29Part00046Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch109
public import GraphCoverageBatch144
public import GraphInputsRow29Part00046Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 29) 8247973560320 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8247973560320 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10992 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8247973560320
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch109.candidate10992_checked

theorem record000_result : Result (29, 8247973560320) :=
  of_direct_small 29 8247973560320 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00046.record000.direct_core, record000_parameters, record000_coverage⟩
#print axioms record000_result

certified_graph_case record001 29 8248094623760 GraphCoverageDescriptions.GraphCoverageBatch144.candidate14470 14

theorem record002_parameters : Parameters record002 (rowOfCode 29) 8250926305536 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8250926305536 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10993 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8250926305536
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch109.candidate10993_checked

theorem record002_result : Result (29, 8250926305536) :=
  of_direct_small 29 8250926305536 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00046.record002.direct_core, record002_parameters, record002_coverage⟩
#print axioms record002_result

certified_graph_case record003 29 8250926370816 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10994 14

certified_graph_case record004 29 8251190546688 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10995 14

certified_graph_case record005 29 8251190611968 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10996 14

certified_graph_case record006 29 8251198410768 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10997 14

theorem record007_parameters : Parameters record007 (rowOfCode 29) 8251215185936 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 8251215185936 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10998 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 8251215185936
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch109.candidate10998_checked

theorem record007_result : Result (29, 8251215185936) :=
  of_direct_small 29 8251215185936 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00046.record007.direct_core, record007_parameters, record007_coverage⟩
#print axioms record007_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00046

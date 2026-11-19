module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00206Checked
public import GraphInputsRow29Part00206Metadata
public import GraphInputsRow29Part00206Frames
public import GraphInputsRow29Part00206Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch119
public import GraphCoverageBatch154
public import GraphInputsRow29Part00206Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00206
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 29140856111104 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15403 14

theorem record001_parameters : Parameters record001 (rowOfCode 29) 29140951007360 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29140951007360 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15404 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 29140951007360
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch154.candidate15404_checked

theorem record001_result : Result (29, 29140951007360) :=
  of_direct_small 29 29140951007360 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00206.record001.direct_core, record001_parameters, record001_coverage⟩

theorem record002_parameters : Parameters record002 (rowOfCode 29) 29141085208704 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29141085208704 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11986 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 29141085208704
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch119.candidate11986_checked

theorem record002_result : Result (29, 29141085208704) :=
  of_direct_small 29 29141085208704 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00206.record002.direct_core, record002_parameters, record002_coverage⟩

certified_graph_case record003 29 29144306421888 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11987 14

certified_graph_case record004 29 29146923696384 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15405 14

certified_graph_case record005 29 29146935726080 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11988 14

certified_graph_case record006 29 29147027013632 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11989 14

theorem record007_parameters : Parameters record007 (rowOfCode 29) 29147067846656 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29147067846656 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15406 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 29147067846656
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch154.candidate15406_checked

theorem record007_result : Result (29, 29147067846656) :=
  of_direct_small 29 29147067846656 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00206.record007.direct_core, record007_parameters, record007_coverage⟩

theorem record008_parameters : Parameters record008 (rowOfCode 29) 29147293302912 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 29147293302912 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11990 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 29147293302912
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch119.candidate11990_checked

theorem record008_result : Result (29, 29147293302912) :=
  of_direct_small 29 29147293302912 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00206.record008.direct_core, record008_parameters, record008_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00206

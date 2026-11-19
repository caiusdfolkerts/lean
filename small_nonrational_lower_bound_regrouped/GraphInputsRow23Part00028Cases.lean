module
prelude
public meta import GraphCases
public import GraphInputsRow23Part00028Checked
public import GraphInputsRow23Part00028Metadata
public import GraphInputsRow23Part00028Frames
public import GraphInputsRow23Part00028Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch059
public import GraphInputsRow23Part00028Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00028
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 23 32488617410560 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05982 6

certified_graph_case record001 23 32491465408512 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05983 6

certified_graph_case record002 23 32492233424896 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05984 6

certified_graph_case record003 23 32505457606912 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05985 6

certified_graph_case record004 23 32514051735552 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05986 6

theorem record005_parameters : Parameters record005 (rowOfCode 23) 32514588540928 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32514588540928 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05987 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 32514588540928
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch059.candidate05987_checked

theorem record005_result : Result (23, 32514588540928) :=
  of_direct_small 23 32514588540928 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00028.record005.direct_core, record005_parameters, record005_coverage⟩
#print axioms record005_result

certified_graph_case record006 23 32515091922944 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05988 6

certified_graph_case record007 23 32522637475840 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05989 6

certified_graph_case record008 23 32522910040064 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05990 6

certified_graph_case record009 23 32523372462080 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05991 6

certified_graph_case record010 23 32523677663232 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05992 6

theorem record011_parameters : Parameters record011 (rowOfCode 23) 32524445679616 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record011_coverage : Coverage record011 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32524445679616 :=
  GraphCoverageDescriptions.coverage_of_checked record011 GraphCoverageDescriptions.GraphCoverageBatch059.candidate05993 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 32524445679616
    (by rfl) record011_cells_exact
    (GraphCoverageDescriptions.small_allowed record011 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch059.candidate05993_checked

theorem record011_result : Result (23, 32524445679616) :=
  of_direct_small 23 32524445679616 (by decide) ⟨record011, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00028.record011.direct_core, record011_parameters, record011_coverage⟩
#print axioms record011_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00028

module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00095Checked
public import GraphInputsRow24Part00095Metadata
public import GraphInputsRow24Part00095Frames
public import GraphInputsRow24Part00095Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch091
public import GraphInputsRow24Part00095Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 24) 25160489115712 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25160489115712 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09179 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25160489115712
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch091.candidate09179_checked

theorem record000_result : Result (24, 25160489115712) :=
  of_direct_small 24 25160489115712 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00095.record000.direct_core, record000_parameters, record000_coverage⟩
#print axioms record000_result

certified_graph_case record001 24 25161596142144 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09180 14

certified_graph_case record002 24 25177115598912 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09181 14

theorem record003_parameters : Parameters record003 (rowOfCode 24) 25177149685760 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25177149685760 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09182 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25177149685760
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch091.candidate09182_checked

theorem record003_result : Result (24, 25177149685760) :=
  of_direct_small 24 25177149685760 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00095.record003.direct_core, record003_parameters, record003_coverage⟩
#print axioms record003_result

certified_graph_case record004 24 25177151766528 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09183 14

certified_graph_case record005 24 25177184796672 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09184 14

certified_graph_case record006 24 25178172170304 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09185 14

theorem record007_parameters : Parameters record007 (rowOfCode 24) 25178239287296 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25178239287296 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09186 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25178239287296
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch091.candidate09186_checked

theorem record007_result : Result (24, 25178239287296) :=
  of_direct_small 24 25178239287296 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00095.record007.direct_core, record007_parameters, record007_coverage⟩
#print axioms record007_result

certified_graph_case record008 24 25178241368064 GraphCoverageDescriptions.GraphCoverageBatch091.candidate09187 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00095

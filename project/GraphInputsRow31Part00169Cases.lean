module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00169Checked
public import GraphInputsRow31Part00169Metadata
public import GraphInputsRow31Part00169Frames
public import GraphInputsRow31Part00169Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch168
public import GraphInputsRow31Part00169Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00169
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 33298210357248 GraphCoverageDescriptions.GraphCoverageBatch168.candidate16880 14

certified_graph_case record001 31 33307471380996 GraphCoverageDescriptions.GraphCoverageBatch168.candidate16881 14

certified_graph_case record002 31 34086003441920 GraphCoverageDescriptions.GraphCoverageBatch168.candidate16882 14

theorem record003_parameters : Parameters record003 (rowOfCode 31) 34120432418816 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34120432418816 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch168.candidate16883 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 34120432418816
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch168.candidate16883_checked

theorem record003_result : Result (31, 34120432418816) :=
  of_direct_small 31 34120432418816 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00169.record003.direct_core, record003_parameters, record003_coverage⟩
#print axioms record003_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00169

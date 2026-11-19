module
prelude
public meta import GraphCases
public import GraphInputsRow26Part00075Checked
public import GraphInputsRow26Part00075Metadata
public import GraphInputsRow26Part00075Frames
public import GraphInputsRow26Part00075Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch102
public import GraphInputsRow26Part00075Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00075
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 26 32676673486848 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10274 14

certified_graph_case record001 26 32693828061184 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10276 14

certified_graph_case record002 26 32712769962240 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10278 14

certified_graph_case record003 26 32712781991936 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10279 14

certified_graph_case record004 26 32713178353664 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10280 14

certified_graph_case record005 26 32715051639040 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10281 14

certified_graph_case record006 26 32715060547584 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10282 14

certified_graph_case record007 26 32715324788736 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10283 14

certified_graph_case record008 26 32716142739456 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10284 14

certified_graph_case record009 26 32717718684176 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10285 14

certified_graph_case record010 26 32725001043968 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10286 14

certified_graph_case record011 26 32728053714976 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10287 14

certified_graph_case record012 26 32748190367744 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10290 14

certified_graph_case record013 26 32780282003712 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10291 14

certified_graph_case record014 26 32780352290816 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10292 14

theorem record015_parameters : Parameters record015 (rowOfCode 26) 32780360613888 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record015_coverage : Coverage record015 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32780360613888 :=
  GraphCoverageDescriptions.coverage_of_checked record015 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10293 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 32780360613888
    (by rfl) record015_cells_exact
    (GraphCoverageDescriptions.small_allowed record015 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch102.candidate10293_checked

theorem record015_result : Result (26, 32780360613888) :=
  of_direct_small 26 32780360613888 (by decide) ⟨record015, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00075.record015.direct_core, record015_parameters, record015_coverage⟩

theorem record016_parameters : Parameters record016 (rowOfCode 26) 32780550471680 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record016_coverage : Coverage record016 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32780550471680 :=
  GraphCoverageDescriptions.coverage_of_checked record016 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10294 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 32780550471680
    (by rfl) record016_cells_exact
    (GraphCoverageDescriptions.small_allowed record016 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch102.candidate10294_checked

theorem record016_result : Result (26, 32780550471680) :=
  of_direct_small 26 32780550471680 (by decide) ⟨record016, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00075.record016.direct_core, record016_parameters, record016_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00075

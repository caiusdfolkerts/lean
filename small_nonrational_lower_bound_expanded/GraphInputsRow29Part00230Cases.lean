module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00230Checked
public import GraphInputsRow29Part00230Metadata
public import GraphInputsRow29Part00230Frames
public import GraphInputsRow29Part00230Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch121
public import GraphCoverageBatch154
public import GraphInputsRow29Part00230Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00230
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 30898560966656 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12117 14

certified_graph_case record001 29 30900687601665 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12118 14

certified_graph_case record002 29 30900817559552 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15475 14

theorem record003_parameters : Parameters record003 (rowOfCode 29) 30900825882624 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 30900825882624 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12119 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 30900825882624
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch121.candidate12119_checked

theorem record003_result : Result (29, 30900825882624) :=
  of_direct_small 29 30900825882624 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00230.record003.direct_core, record003_parameters, record003_coverage⟩

certified_graph_case record004 29 30900947518208 GraphCoverageDescriptions.GraphCoverageBatch121.candidate12120 14

theorem record005_parameters : Parameters record005 (rowOfCode 29) 30903096115200 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 30903096115200 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch154.candidate15476 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 30903096115200
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch154.candidate15476_checked

theorem record005_result : Result (29, 30903096115200) :=
  of_direct_small 29 30903096115200 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00230.record005.direct_core, record005_parameters, record005_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00230

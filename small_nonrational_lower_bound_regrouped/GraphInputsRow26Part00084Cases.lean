module
prelude
public meta import GraphCases
public import GraphInputsRow26Part00084Checked
public import GraphInputsRow26Part00084Metadata
public import GraphInputsRow26Part00084Frames
public import GraphInputsRow26Part00084Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch104
public import GraphInputsRow26Part00084Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 26 34673288315136 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10444 14

certified_graph_case record001 26 34673556783104 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10445 14

theorem record002_parameters : Parameters record002 (rowOfCode 26) 34673565106176 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34673565106176 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10446 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 34673565106176
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch104.candidate10446_checked

theorem record002_result : Result (26, 34673565106176) :=
  of_direct_small 26 34673565106176 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00084.record002.direct_core, record002_parameters, record002_coverage⟩
#print axioms record002_result

certified_graph_case record003 26 34674076553216 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10447 14

certified_graph_case record004 26 34674344886528 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10448 14

certified_graph_case record005 26 34674382536704 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10449 14

theorem record006_parameters : Parameters record006 (rowOfCode 26) 34674655100928 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34674655100928 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10450 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 34674655100928
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch104.candidate10450_checked

theorem record006_result : Result (26, 34674655100928) :=
  of_direct_small 26 34674655100928 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00084.record006.direct_core, record006_parameters, record006_coverage⟩
#print axioms record006_result

certified_graph_case record007 26 34675150029312 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10451 14

certified_graph_case record008 26 34675150553088 GraphCoverageDescriptions.GraphCoverageBatch104.candidate10452 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00084

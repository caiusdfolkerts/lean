module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00067Checked
public import GraphInputsRow31Part00067Metadata
public import GraphInputsRow31Part00067Frames
public import GraphInputsRow31Part00067Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch161
public import GraphInputsRow31Part00067Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00067
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 13281453473792 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16128 14

certified_graph_case record001 31 13289434652704 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16129 14

certified_graph_case record002 31 13308761473792 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16130 14

certified_graph_case record003 31 13316818796800 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16131 14

certified_graph_case record004 31 13317355667456 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16132 14

certified_graph_case record005 31 13317363990528 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16133 14

certified_graph_case record006 31 13323793859104 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16134 14

certified_graph_case record007 31 13338826776832 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16135 14

certified_graph_case record008 31 13341444604160 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16136 14

theorem record009_parameters : Parameters record009 (rowOfCode 31) 13341452992512 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 13341452992512 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16137 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 13341452992512
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.small_allowed record009 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch161.candidate16137_checked

theorem record009_result : Result (31, 13341452992512) :=
  of_direct_small 31 13341452992512 (by decide) ⟨record009, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00067.record009.direct_core, record009_parameters, record009_coverage⟩

certified_graph_case record010 31 13341856636928 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16138 14

certified_graph_case record011 31 13341914308864 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16139 14

theorem record012_parameters : Parameters record012 (rowOfCode 31) 13342987526400 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record012_coverage : Coverage record012 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 13342987526400 :=
  GraphCoverageDescriptions.coverage_of_checked record012 GraphCoverageDescriptions.GraphCoverageBatch161.candidate16140 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 13342987526400
    (by rfl) record012_cells_exact
    (GraphCoverageDescriptions.small_allowed record012 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch161.candidate16140_checked

theorem record012_result : Result (31, 13342987526400) :=
  of_direct_small 31 13342987526400 (by decide) ⟨record012, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00067.record012.direct_core, record012_parameters, record012_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00067

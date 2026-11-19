module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00085Checked
public import GraphInputsRow31Part00085Metadata
public import GraphInputsRow31Part00085Frames
public import GraphInputsRow31Part00085Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch163
public import GraphInputsRow31Part00085Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00085
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 17052135915520 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16306 14

theorem record001_parameters : Parameters record001 (rowOfCode 31) 17052664332800 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 17052664332800 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16307 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 17052664332800
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch163.candidate16307_checked

theorem record001_result : Result (31, 17052664332800) :=
  of_direct_small 31 17052664332800 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00085.record001.direct_core, record001_parameters, record001_coverage⟩

certified_graph_case record002 31 17052672720896 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16308 14

certified_graph_case record003 31 17060721655808 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16309 14

certified_graph_case record004 31 17061258461184 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16310 14

certified_graph_case record005 31 17061489672192 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16311 14

theorem record006_parameters : Parameters record006 (rowOfCode 31) 17068200169488 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 17068200169488 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16312 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 17068200169488
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch163.candidate16312_checked

theorem record006_result : Result (31, 17068200169488) :=
  of_direct_small 31 17068200169488 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00085.record006.direct_core, record006_parameters, record006_coverage⟩

certified_graph_case record007 31 17068234178560 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16313 14

certified_graph_case record008 31 17120016531456 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16314 14

certified_graph_case record009 31 17179886551296 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16315 14

certified_graph_case record010 31 17181219815424 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16316 14

certified_graph_case record011 31 17190078119936 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16317 14

certified_graph_case record012 31 17197049186320 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16318 14

certified_graph_case record013 31 17197066420224 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16319 14

certified_graph_case record014 31 17197603225600 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16320 14

certified_graph_case record015 31 17198122795524 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16321 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00085

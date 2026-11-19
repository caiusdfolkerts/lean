module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00098Checked
public import GraphInputsRow29Part00098Metadata
public import GraphInputsRow29Part00098Frames
public import GraphInputsRow29Part00098Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch114
public import GraphInputsRow29Part00098Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00098
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 16980430028800 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11448 14

certified_graph_case record001 29 16985119260672 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11449 14

certified_graph_case record002 29 16986671153152 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11450 14

certified_graph_case record003 29 17003842633728 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11451 14

theorem record004_parameters : Parameters record004 (rowOfCode 29) 17042481381632 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 17042481381632 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11452 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 17042481381632
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch114.candidate11452_checked

theorem record004_result : Result (29, 17042481381632) :=
  of_direct_small 29 17042481381632 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00098.record004.direct_core, record004_parameters, record004_coverage⟩
#print axioms record004_result

certified_graph_case record005 29 17042481446912 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11453 14

certified_graph_case record006 29 17042485022976 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11454 14

certified_graph_case record007 29 17042485088256 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11455 14

certified_graph_case record008 29 17042493147152 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11456 14

certified_graph_case record009 29 17042724098064 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11457 14

theorem record010_parameters : Parameters record010 (rowOfCode 29) 17042724358160 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record010_coverage : Coverage record010 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 17042724358160 :=
  GraphCoverageDescriptions.coverage_of_checked record010 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11458 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 17042724358160
    (by rfl) record010_cells_exact
    (GraphCoverageDescriptions.small_allowed record010 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch114.candidate11458_checked

theorem record010_result : Result (29, 17042724358160) :=
  of_direct_small 29 17042724358160 (by decide) ⟨record010, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00098.record010.direct_core, record010_parameters, record010_coverage⟩
#print axioms record010_result

certified_graph_case record011 29 17043558564352 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11459 14

certified_graph_case record012 29 17043780929552 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11460 14

certified_graph_case record013 29 17043798097921 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11461 14

certified_graph_case record014 29 17043798163456 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11462 14

certified_graph_case record015 29 17044058177792 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11463 14

certified_graph_case record016 29 17044066566144 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11464 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00098

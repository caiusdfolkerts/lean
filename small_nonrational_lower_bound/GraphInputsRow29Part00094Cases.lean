module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00094Checked
public import GraphInputsRow29Part00094Metadata
public import GraphInputsRow29Part00094Frames
public import GraphInputsRow29Part00094Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch114
public import GraphCoverageBatch147
public import GraphInputsRow29Part00094Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 29) 16536295444736 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 16536295444736 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14751 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 16536295444736
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch147.candidate14751_checked

theorem record000_result : Result (29, 16536295444736) :=
  of_direct_small 29 16536295444736 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00094.record000.direct_core, record000_parameters, record000_coverage⟩
#print axioms record000_result

certified_graph_case record001 29 16536836309248 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14752 14

certified_graph_case record002 29 16537108938752 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14753 14

theorem record003_parameters : Parameters record003 (rowOfCode 29) 16537368920832 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 16537368920832 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14754 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 16537368920832
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch147.candidate14754_checked

theorem record003_result : Result (29, 16537368920832) :=
  of_direct_small 29 16537368920832 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00094.record003.direct_core, record003_parameters, record003_coverage⟩
#print axioms record003_result

certified_graph_case record004 29 16537373179904 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11409 14

certified_graph_case record005 29 16537381502976 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11410 14

certified_graph_case record006 29 16537505300480 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14755 14

certified_graph_case record007 29 16539956871424 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14756 14

certified_graph_case record008 29 16540724953088 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14757 14

certified_graph_case record009 29 16544616943872 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14758 14

certified_graph_case record010 29 16544768213120 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14759 14

certified_graph_case record011 29 16544773967872 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14760 14

certified_graph_case record012 29 16544885379200 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11411 14

certified_graph_case record013 29 16545958855296 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14761 14

certified_graph_case record014 29 16549314298384 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14762 14

certified_graph_case record015 29 16608915423232 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14763 14

certified_graph_case record016 29 16609452228608 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14764 14

certified_graph_case record017 29 16632420827136 GraphCoverageDescriptions.GraphCoverageBatch114.candidate11412 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094

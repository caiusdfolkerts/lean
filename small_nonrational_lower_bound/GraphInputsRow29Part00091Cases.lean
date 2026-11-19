module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00091Checked
public import GraphInputsRow29Part00091Metadata
public import GraphInputsRow29Part00091Frames
public import GraphInputsRow29Part00091Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch113
public import GraphCoverageBatch147
public import GraphInputsRow29Part00091Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 16128415891456 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11386 14

certified_graph_case record001 29 16493834699008 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11387 14

certified_graph_case record002 29 16493834764288 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11388 14

certified_graph_case record003 29 16493838340352 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14739 14

certified_graph_case record004 29 16494977618176 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11389 14

certified_graph_case record005 29 16494977683456 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11390 14

certified_graph_case record006 29 16494985482256 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11391 14

theorem record007_parameters : Parameters record007 (rowOfCode 29) 16495002257424 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 16495002257424 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11392 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 16495002257424
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch113.candidate11392_checked

theorem record007_result : Result (29, 16495002257424) :=
  of_direct_small 29 16495002257424 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00091.record007.direct_core, record007_parameters, record007_coverage⟩
#print axioms record007_result

theorem record008_parameters : Parameters record008 (rowOfCode 29) 16495109738752 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 16495109738752 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11393 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 16495109738752
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch113.candidate11393_checked

theorem record008_result : Result (29, 16495109738752) :=
  of_direct_small 29 16495109738752 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00091.record008.direct_core, record008_parameters, record008_coverage⟩
#print axioms record008_result

theorem record009_parameters : Parameters record009 (rowOfCode 29) 16496075997185 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 16496075997185 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch113.candidate11394 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 16496075997185
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.small_allowed record009 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch113.candidate11394_checked

theorem record009_result : Result (29, 16496075997185) :=
  of_direct_small 29 16496075997185 (by decide) ⟨record009, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00091.record009.direct_core, record009_parameters, record009_coverage⟩
#print axioms record009_result

certified_graph_case record010 29 16496208183296 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14740 14

certified_graph_case record011 29 16496468197632 GraphCoverageDescriptions.GraphCoverageBatch147.candidate14741 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091

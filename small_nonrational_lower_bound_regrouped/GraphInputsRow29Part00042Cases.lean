module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00042Checked
public import GraphInputsRow29Part00042Metadata
public import GraphInputsRow29Part00042Frames
public import GraphInputsRow29Part00042Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch109
public import GraphCoverageBatch144
public import GraphInputsRow29Part00042Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00042
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 7598090813440 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10950 14

certified_graph_case record001 29 7598355054592 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10951 14

certified_graph_case record002 29 7598363377664 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10952 14

certified_graph_case record003 29 7598602453512 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10953 14

certified_graph_case record004 29 7598602780672 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10954 14

certified_graph_case record005 29 7607200776192 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10955 14

certified_graph_case record006 29 7611085029376 GraphCoverageDescriptions.GraphCoverageBatch144.candidate14452 14

certified_graph_case record007 29 7611237826560 GraphCoverageDescriptions.GraphCoverageBatch144.candidate14453 14

theorem record008_parameters : Parameters record008 (rowOfCode 29) 7611241988096 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 7611241988096 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch109.candidate10956 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 7611241988096
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch109.candidate10956_checked

theorem record008_result : Result (29, 7611241988096) :=
  of_direct_small 29 7611241988096 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00042.record008.direct_core, record008_parameters, record008_coverage⟩
#print axioms record008_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00042

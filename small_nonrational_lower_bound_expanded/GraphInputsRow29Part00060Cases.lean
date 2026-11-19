module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00060Checked
public import GraphInputsRow29Part00060Metadata
public import GraphInputsRow29Part00060Frames
public import GraphInputsRow29Part00060Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch111
public import GraphCoverageBatch145
public import GraphInputsRow29Part00060Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00060
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 11283294326816 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11111 14

certified_graph_case record001 29 11317654061057 GraphCoverageDescriptions.GraphCoverageBatch145.candidate14577 14

certified_graph_case record002 29 11380325384192 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11112 14

certified_graph_case record003 29 11384226054144 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11113 14

certified_graph_case record004 29 11384618254336 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11114 14

certified_graph_case record005 29 11398912442496 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11115 14

certified_graph_case record006 29 11401129132032 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11116 14

theorem record007_parameters : Parameters record007 (rowOfCode 29) 11401397534720 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 11401397534720 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11117 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 11401397534720
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch111.candidate11117_checked

theorem record007_result : Result (29, 11401397534720) :=
  of_direct_small 29 11401397534720 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00060.record007.direct_core, record007_parameters, record007_coverage⟩

certified_graph_case record008 29 11448373772544 GraphCoverageDescriptions.GraphCoverageBatch145.candidate14578 14

theorem record009_parameters : Parameters record009 (rowOfCode 29) 11448642240512 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 11448642240512 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch145.candidate14579 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 11448642240512
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.small_allowed record009 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch145.candidate14579_checked

theorem record009_result : Result (29, 11448642240512) :=
  of_direct_small 29 11448642240512 (by decide) ⟨record009, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00060.record009.direct_core, record009_parameters, record009_coverage⟩

certified_graph_case record010 29 11448650563584 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11118 14

certified_graph_case record011 29 11448910643200 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11119 14

certified_graph_case record012 29 11449042763776 GraphCoverageDescriptions.GraphCoverageBatch145.candidate14580 14

theorem record013_parameters : Parameters record013 (rowOfCode 29) 11452943433728 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record013_coverage : Coverage record013 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 11452943433728 :=
  GraphCoverageDescriptions.coverage_of_checked record013 GraphCoverageDescriptions.GraphCoverageBatch111.candidate11120 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 11452943433728
    (by rfl) record013_cells_exact
    (GraphCoverageDescriptions.small_allowed record013 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch111.candidate11120_checked

theorem record013_result : Result (29, 11452943433728) :=
  of_direct_small 29 11452943433728 (by decide) ⟨record013, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00060.record013.direct_core, record013_parameters, record013_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00060

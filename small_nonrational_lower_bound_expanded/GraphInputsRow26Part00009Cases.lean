module
prelude
public meta import GraphCases
public import GraphInputsRow26Part00009Checked
public import GraphInputsRow26Part00009Metadata
public import GraphInputsRow26Part00009Frames
public import GraphInputsRow26Part00009Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch066
public import GraphCoverageBatch125
public import GraphInputsRow26Part00009Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 26 6701781664000 GraphCoverageDescriptions.GraphCoverageBatch125.candidate12564 14

certified_graph_case record001 26 6727061962752 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06619 14

certified_graph_case record002 26 6727065928960 GraphCoverageDescriptions.GraphCoverageBatch125.candidate12565 14

certified_graph_case record003 26 6727206436865 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06620 14

certified_graph_case record004 26 6727607025664 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06621 14

certified_graph_case record005 26 6790396870656 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06622 14

certified_graph_case record006 26 6791486472192 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06625 14

certified_graph_case record007 26 6791630946305 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06626 14

certified_graph_case record008 26 6791631011840 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06627 14

certified_graph_case record009 26 6823698661632 GraphCoverageDescriptions.GraphCoverageBatch125.candidate12566 14

certified_graph_case record010 26 6837674279168 GraphCoverageDescriptions.GraphCoverageBatch125.candidate12567 14

theorem record011_parameters : Parameters record011 (rowOfCode 26) 6837682405384 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record011_coverage : Coverage record011 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 6837682405384 :=
  GraphCoverageDescriptions.coverage_of_checked record011 GraphCoverageDescriptions.GraphCoverageBatch125.candidate12568 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 6837682405384
    (by rfl) record011_cells_exact
    (GraphCoverageDescriptions.small_allowed record011 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch125.candidate12568_checked

theorem record011_result : Result (26, 6837682405384) :=
  of_direct_small 26 6837682405384 (by decide) ⟨record011, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00009.record011.direct_core, record011_parameters, record011_coverage⟩

theorem record012_parameters : Parameters record012 (rowOfCode 26) 6838144827400 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record012_coverage : Coverage record012 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 6838144827400 :=
  GraphCoverageDescriptions.coverage_of_checked record012 GraphCoverageDescriptions.GraphCoverageBatch125.candidate12569 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 6838144827400
    (by rfl) record012_cells_exact
    (GraphCoverageDescriptions.small_allowed record012 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch125.candidate12569_checked

theorem record012_result : Result (26, 6838144827400) :=
  of_direct_small 26 6838144827400 (by decide) ⟨record012, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00009.record012.direct_core, record012_parameters, record012_coverage⟩

theorem record013_parameters : Parameters record013 (rowOfCode 26) 6839878254600 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record013_coverage : Coverage record013 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 6839878254600 :=
  GraphCoverageDescriptions.coverage_of_checked record013 GraphCoverageDescriptions.GraphCoverageBatch125.candidate12570 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 6839878254600
    (by rfl) record013_cells_exact
    (GraphCoverageDescriptions.small_allowed record013 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch125.candidate12570_checked

theorem record013_result : Result (26, 6839878254600) :=
  of_direct_small 26 6839878254600 (by decide) ⟨record013, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00009.record013.direct_core, record013_parameters, record013_coverage⟩

certified_graph_case record014 26 6841954404608 GraphCoverageDescriptions.GraphCoverageBatch125.candidate12571 14

certified_graph_case record015 26 6854837239816 GraphCoverageDescriptions.GraphCoverageBatch125.candidate12572 14

certified_graph_case record016 26 6866188894208 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06629 14

certified_graph_case record017 26 6866453135360 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06630 14

certified_graph_case record018 26 6877489438976 GraphCoverageDescriptions.GraphCoverageBatch125.candidate12573 14

certified_graph_case record019 26 6910890254592 GraphCoverageDescriptions.GraphCoverageBatch125.candidate12574 14

certified_graph_case record020 26 6912022249472 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06631 14

certified_graph_case record021 26 6920335491072 GraphCoverageDescriptions.GraphCoverageBatch125.candidate12575 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00009

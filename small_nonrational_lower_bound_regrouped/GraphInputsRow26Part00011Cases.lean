module
prelude
public meta import GraphCases
public import GraphInputsRow26Part00011Checked
public import GraphInputsRow26Part00011Metadata
public import GraphInputsRow26Part00011Frames
public import GraphInputsRow26Part00011Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch066
public import GraphCoverageBatch067
public import GraphCoverageBatch125
public import GraphCoverageBatch126
public import GraphInputsRow26Part00011Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 26 7147988009344 GraphCoverageDescriptions.GraphCoverageBatch125.candidate12583 14

certified_graph_case record001 26 7149128847744 GraphCoverageDescriptions.GraphCoverageBatch125.candidate12584 14

theorem record002_parameters : Parameters record002 (rowOfCode 26) 7149260968320 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 7149260968320 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch125.candidate12585 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 7149260968320
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch125.candidate12585_checked

theorem record002_result : Result (26, 7149260968320) :=
  of_direct_small 26 7149260968320 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00011.record002.direct_core, record002_parameters, record002_coverage⟩
#print axioms record002_result

certified_graph_case record003 26 7149263065408 GraphCoverageDescriptions.GraphCoverageBatch125.candidate12586 14

certified_graph_case record004 26 7149531468096 GraphCoverageDescriptions.GraphCoverageBatch125.candidate12587 14

certified_graph_case record005 26 7155970756992 GraphCoverageDescriptions.GraphCoverageBatch125.candidate12588 14

certified_graph_case record006 26 7155970773312 GraphCoverageDescriptions.GraphCoverageBatch125.candidate12589 14

certified_graph_case record007 26 7186046615568 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06687 14

certified_graph_case record008 26 7186826724100 GraphCoverageDescriptions.GraphCoverageBatch125.candidate12590 14

certified_graph_case record009 26 7190339485712 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06689 14

certified_graph_case record010 26 7191532765184 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06690 14

certified_graph_case record011 26 7207773016128 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06691 14

certified_graph_case record012 26 7224698175504 GraphCoverageDescriptions.GraphCoverageBatch125.candidate12591 14

certified_graph_case record013 26 7289122684944 GraphCoverageDescriptions.GraphCoverageBatch125.candidate12592 14

certified_graph_case record014 26 7302571720704 GraphCoverageDescriptions.GraphCoverageBatch125.candidate12593 14

certified_graph_case record015 26 7375276744704 GraphCoverageDescriptions.GraphCoverageBatch067.candidate06700 14

certified_graph_case record016 26 7424014647312 GraphCoverageDescriptions.GraphCoverageBatch067.candidate06701 14

certified_graph_case record017 26 7448724275200 GraphCoverageDescriptions.GraphCoverageBatch067.candidate06704 14

certified_graph_case record018 26 7518138925568 GraphCoverageDescriptions.GraphCoverageBatch067.candidate06706 14

certified_graph_case record019 26 7525076664320 GraphCoverageDescriptions.GraphCoverageBatch067.candidate06707 14

certified_graph_case record020 26 7525348935808 GraphCoverageDescriptions.GraphCoverageBatch125.candidate12594 14

certified_graph_case record021 26 7533922092040 GraphCoverageDescriptions.GraphCoverageBatch125.candidate12595 14

certified_graph_case record022 26 7533938868225 GraphCoverageDescriptions.GraphCoverageBatch125.candidate12596 14

certified_graph_case record023 26 7551374590464 GraphCoverageDescriptions.GraphCoverageBatch067.candidate06708 14

theorem record024_parameters : Parameters record024 (rowOfCode 26) 7559194132736 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record024_coverage : Coverage record024 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 7559194132736 :=
  GraphCoverageDescriptions.coverage_of_checked record024 GraphCoverageDescriptions.GraphCoverageBatch125.candidate12597 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 7559194132736
    (by rfl) record024_cells_exact
    (GraphCoverageDescriptions.small_allowed record024 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch125.candidate12597_checked

theorem record024_result : Result (26, 7559194132736) :=
  of_direct_small 26 7559194132736 (by decide) ⟨record024, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00011.record024.direct_core, record024_parameters, record024_coverage⟩
#print axioms record024_result

certified_graph_case record025 26 7559196016648 GraphCoverageDescriptions.GraphCoverageBatch125.candidate12598 14

certified_graph_case record026 26 7559198097416 GraphCoverageDescriptions.GraphCoverageBatch125.candidate12599 14

certified_graph_case record027 26 7560285554944 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12600 14

certified_graph_case record028 26 7560285618184 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12601 14

certified_graph_case record029 26 7560302199552 GraphCoverageDescriptions.GraphCoverageBatch126.candidate12602 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011

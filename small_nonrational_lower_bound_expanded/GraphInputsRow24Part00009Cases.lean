module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00009Checked
public import GraphInputsRow24Part00009Metadata
public import GraphInputsRow24Part00009Frames
public import GraphInputsRow24Part00009Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch066
public import GraphInputsRow24Part00009Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 6379649631232 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06602 14

certified_graph_case record001 24 6379918065664 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06603 14

certified_graph_case record002 24 6425833472000 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06604 14

certified_graph_case record003 24 6443268835328 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06605 14

certified_graph_case record004 24 6447563800576 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06606 14

certified_graph_case record005 24 6451871350784 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06607 14

certified_graph_case record006 24 6456149540864 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06608 14

certified_graph_case record007 24 6487088824320 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06609 14

certified_graph_case record008 24 6511854094336 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06610 14

certified_graph_case record009 24 6524592390144 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06611 14

certified_graph_case record010 24 6524600713216 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06612 14

certified_graph_case record011 24 6548361314304 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06613 14

certified_graph_case record012 24 6559027429376 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06614 14

certified_graph_case record013 24 6637144342784 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06615 14

certified_graph_case record014 24 6638555725840 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06616 14

certified_graph_case record015 24 6711570169856 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06617 14

certified_graph_case record016 24 6727061897472 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06618 14

certified_graph_case record017 24 6727061962752 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06619 14

certified_graph_case record018 24 6727206436865 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06620 14

certified_graph_case record019 24 6727607025664 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06621 14

theorem record020_parameters : Parameters record020 (rowOfCode 24) 6790396870656 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record020_coverage : Coverage record020 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 6790396870656 :=
  GraphCoverageDescriptions.coverage_of_checked record020 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06622 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 6790396870656
    (by rfl) record020_cells_exact
    (GraphCoverageDescriptions.small_allowed record020 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch066.candidate06622_checked

theorem record020_result : Result (24, 6790396870656) :=
  of_direct_small 24 6790396870656 (by decide) ⟨record020, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00009.record020.direct_core, record020_parameters, record020_coverage⟩

certified_graph_case record021 24 6791161192512 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06623 14

certified_graph_case record022 24 6791486406912 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06624 14

theorem record023_parameters : Parameters record023 (rowOfCode 24) 6791486472192 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record023_coverage : Coverage record023 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 6791486472192 :=
  GraphCoverageDescriptions.coverage_of_checked record023 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06625 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 6791486472192
    (by rfl) record023_cells_exact
    (GraphCoverageDescriptions.small_allowed record023 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch066.candidate06625_checked

theorem record023_result : Result (24, 6791486472192) :=
  of_direct_small 24 6791486472192 (by decide) ⟨record023, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00009.record023.direct_core, record023_parameters, record023_coverage⟩

certified_graph_case record024 24 6791630946305 GraphCoverageDescriptions.GraphCoverageBatch066.candidate06626 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00009

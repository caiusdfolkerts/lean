module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00155Checked
public import GraphInputsRow29Part00155Metadata
public import GraphInputsRow29Part00155Frames
public import GraphInputsRow29Part00155Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch117
public import GraphCoverageBatch152
public import GraphInputsRow29Part00155Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00155
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 29) 24786294079744 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24786294079744 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15203 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24786294079744
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch152.candidate15203_checked

theorem record000_result : Result (29, 24786294079744) :=
  of_direct_small 29 24786294079744 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00155.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 29 24787062161408 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15204 14

certified_graph_case record002 29 24791222587520 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15205 14

certified_graph_case record003 29 24799947014144 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15206 14

certified_graph_case record004 29 24825515217024 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15207 14

certified_graph_case record005 29 24826588693120 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15208 14

certified_graph_case record006 29 24855252631552 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15209 14

certified_graph_case record007 29 24883698925568 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15210 14

certified_graph_case record008 29 24886720397312 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15211 14

certified_graph_case record009 29 24886728720384 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15212 14

certified_graph_case record010 29 24889940049920 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15213 14

certified_graph_case record011 29 24894773428480 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15214 14

certified_graph_case record012 29 24894909775872 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15215 14

certified_graph_case record013 29 24894918098944 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11778 14

certified_graph_case record014 29 24895041896448 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15216 14

certified_graph_case record015 29 24895050219520 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15217 14

theorem record016_parameters : Parameters record016 (rowOfCode 29) 24895510560768 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record016_coverage : Coverage record016 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24895510560768 :=
  GraphCoverageDescriptions.coverage_of_checked record016 GraphCoverageDescriptions.GraphCoverageBatch117.candidate11779 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24895510560768
    (by rfl) record016_cells_exact
    (GraphCoverageDescriptions.small_allowed record016 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch117.candidate11779_checked

theorem record016_result : Result (29, 24895510560768) :=
  of_direct_small 29 24895510560768 (by decide) ⟨record016, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00155.record016.direct_core, record016_parameters, record016_coverage⟩

certified_graph_case record017 29 24895813615872 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15218 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00155

module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00162Checked
public import GraphInputsRow29Part00162Metadata
public import GraphInputsRow29Part00162Frames
public import GraphInputsRow29Part00162Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch118
public import GraphCoverageBatch152
public import GraphInputsRow29Part00162Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00162
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 25333472428032 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11808 14

certified_graph_case record001 29 25336047796480 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15237 14

certified_graph_case record002 29 25336683757568 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15238 14

certified_graph_case record003 29 25341517136128 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15239 14

certified_graph_case record004 29 25341785604096 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11809 14

certified_graph_case record005 29 25341793927168 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11810 14

certified_graph_case record006 29 25342188208128 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15240 14

certified_graph_case record007 29 25345407860736 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15241 14

certified_graph_case record008 29 25348932649216 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15242 14

certified_graph_case record009 29 25363463864320 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15243 14

theorem record010_parameters : Parameters record010 (rowOfCode 29) 25363472187392 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record010_coverage : Coverage record010 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25363472187392 :=
  GraphCoverageDescriptions.coverage_of_checked record010 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11811 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25363472187392
    (by rfl) record010_cells_exact
    (GraphCoverageDescriptions.small_allowed record010 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch118.candidate11811_checked

theorem record010_result : Result (29, 25363472187392) :=
  of_direct_small 29 25363472187392 (by decide) ⟨record010, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00162.record010.direct_core, record010_parameters, record010_coverage⟩

certified_graph_case record011 29 25363967181056 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15244 14

certified_graph_case record012 29 25364735262720 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11812 14

certified_graph_case record013 29 25367219863808 GraphCoverageDescriptions.GraphCoverageBatch152.candidate15245 14

certified_graph_case record014 29 25367360372736 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11813 14

theorem record015_parameters : Parameters record015 (rowOfCode 29) 25367756734464 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record015_coverage : Coverage record015 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25367756734464 :=
  GraphCoverageDescriptions.coverage_of_checked record015 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11814 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25367756734464
    (by rfl) record015_cells_exact
    (GraphCoverageDescriptions.small_allowed record015 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch118.candidate11814_checked

theorem record015_result : Result (29, 25367756734464) :=
  of_direct_small 29 25367756734464 (by decide) ⟨record015, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00162.record015.direct_core, record015_parameters, record015_coverage⟩

theorem record016_parameters : Parameters record016 (rowOfCode 29) 25367765057536 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record016_coverage : Coverage record016 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 25367765057536 :=
  GraphCoverageDescriptions.coverage_of_checked record016 GraphCoverageDescriptions.GraphCoverageBatch118.candidate11815 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 25367765057536
    (by rfl) record016_cells_exact
    (GraphCoverageDescriptions.small_allowed record016 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch118.candidate11815_checked

theorem record016_result : Result (29, 25367765057536) :=
  of_direct_small 29 25367765057536 (by decide) ⟨record016, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00162.record016.direct_core, record016_parameters, record016_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00162

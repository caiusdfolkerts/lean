module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00118Checked
public import GraphInputsRow31Part00118Metadata
public import GraphInputsRow31Part00118Frames
public import GraphInputsRow31Part00118Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch165
public import GraphCoverageBatch166
public import GraphInputsRow31Part00118Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00118
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 31) 26513639505920 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 26513639505920 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch165.candidate16596 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 26513639505920
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch165.candidate16596_checked

theorem record000_result : Result (31, 26513639505920) :=
  of_direct_small 31 26513639505920 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00118.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 31 26535995129856 GraphCoverageDescriptions.GraphCoverageBatch165.candidate16597 14

certified_graph_case record002 31 26537035317248 GraphCoverageDescriptions.GraphCoverageBatch165.candidate16598 14

certified_graph_case record003 31 26571360583680 GraphCoverageDescriptions.GraphCoverageBatch165.candidate16599 14

certified_graph_case record004 31 26571622645760 GraphCoverageDescriptions.GraphCoverageBatch166.candidate16600 14

certified_graph_case record005 31 26580210418240 GraphCoverageDescriptions.GraphCoverageBatch166.candidate16601 14

certified_graph_case record006 31 26616718696448 GraphCoverageDescriptions.GraphCoverageBatch166.candidate16602 14

certified_graph_case record007 31 26716980412544 GraphCoverageDescriptions.GraphCoverageBatch166.candidate16603 14

certified_graph_case record008 31 26717248847872 GraphCoverageDescriptions.GraphCoverageBatch166.candidate16604 14

certified_graph_case record009 31 26717253009408 GraphCoverageDescriptions.GraphCoverageBatch166.candidate16605 14

theorem record010_parameters : Parameters record010 (rowOfCode 31) 26757714428032 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record010_coverage : Coverage record010 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 26757714428032 :=
  GraphCoverageDescriptions.coverage_of_checked record010 GraphCoverageDescriptions.GraphCoverageBatch166.candidate16606 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 26757714428032
    (by rfl) record010_cells_exact
    (GraphCoverageDescriptions.small_allowed record010 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch166.candidate16606_checked

theorem record010_result : Result (31, 26757714428032) :=
  of_direct_small 31 26757714428032 (by decide) ⟨record010, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00118.record010.direct_core, record010_parameters, record010_coverage⟩

certified_graph_case record011 31 27015630037248 GraphCoverageDescriptions.GraphCoverageBatch166.candidate16607 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00118

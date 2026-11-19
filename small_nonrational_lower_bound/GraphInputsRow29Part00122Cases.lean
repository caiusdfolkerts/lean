module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00122Checked
public import GraphInputsRow29Part00122Metadata
public import GraphInputsRow29Part00122Frames
public import GraphInputsRow29Part00122Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch116
public import GraphCoverageBatch149
public import GraphInputsRow29Part00122Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00122
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 20740397236352 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14982 14

certified_graph_case record001 29 20744692187264 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11620 14

theorem record002_parameters : Parameters record002 (rowOfCode 29) 20748987170816 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 20748987170816 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11621 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 20748987170816
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch116.candidate11621_checked

theorem record002_result : Result (29, 20748987170816) :=
  of_direct_small 29 20748987170816 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00122.record002.direct_core, record002_parameters, record002_coverage⟩
#print axioms record002_result

certified_graph_case record003 29 20749255573504 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11622 14

certified_graph_case record004 29 20758856269824 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11623 14

certified_graph_case record005 29 20792091934720 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14983 14

certified_graph_case record006 29 20792608063488 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11624 14

certified_graph_case record007 29 20800937656320 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11625 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00122

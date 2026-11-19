module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00126Checked
public import GraphInputsRow29Part00126Metadata
public import GraphInputsRow29Part00126Frames
public import GraphInputsRow29Part00126Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch116
public import GraphCoverageBatch149
public import GraphInputsRow29Part00126Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00126
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 21382631063552 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11646 14

certified_graph_case record001 29 21383167868928 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11647 14

certified_graph_case record002 29 21384711438336 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11648 14

certified_graph_case record003 29 21397596291072 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11649 14

theorem record004_parameters : Parameters record004 (rowOfCode 29) 21401891241984 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 21401891241984 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11650 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 21401891241984
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch116.candidate11650_checked

theorem record004_result : Result (29, 21401891241984) :=
  of_direct_small 29 21401891241984 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00126.record004.direct_core, record004_parameters, record004_coverage⟩
#print axioms record004_result

certified_graph_case record005 29 21402023362560 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11651 14

certified_graph_case record006 29 21441704132864 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14990 14

certified_graph_case record007 29 21446017483008 GraphCoverageDescriptions.GraphCoverageBatch149.candidate14991 14

certified_graph_case record008 29 21446426394624 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11652 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00126

module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00104Checked
public import GraphInputsRow29Part00104Metadata
public import GraphInputsRow29Part00104Frames
public import GraphInputsRow29Part00104Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch115
public import GraphCoverageBatch148
public import GraphInputsRow29Part00104Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 17783727341824 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14814 14

certified_graph_case record001 29 17784129994816 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11535 14

certified_graph_case record002 29 17786141155456 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14815 14

certified_graph_case record003 29 17786277470272 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11536 14

certified_graph_case record004 29 17839352250624 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14816 14

certified_graph_case record005 29 17856532119552 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11537 14

certified_graph_case record006 29 17914990174336 GraphCoverageDescriptions.GraphCoverageBatch148.candidate14817 14

theorem record007_parameters : Parameters record007 (rowOfCode 29) 18143305605440 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 18143305605440 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch115.candidate11538 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 18143305605440
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch115.candidate11538_checked

theorem record007_result : Result (29, 18143305605440) :=
  of_direct_small 29 18143305605440 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00104.record007.direct_core, record007_parameters, record007_coverage⟩
#print axioms record007_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00104

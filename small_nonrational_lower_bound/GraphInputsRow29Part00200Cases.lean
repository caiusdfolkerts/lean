module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00200Checked
public import GraphInputsRow29Part00200Metadata
public import GraphInputsRow29Part00200Frames
public import GraphInputsRow29Part00200Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch119
public import GraphCoverageBatch153
public import GraphInputsRow29Part00200Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00200
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 28830523752448 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11960 14

certified_graph_case record001 29 28830527913984 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11961 14

certified_graph_case record002 29 28830639357952 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15389 14

certified_graph_case record003 29 28838968950784 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15390 14

certified_graph_case record004 29 28845018202240 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11962 14

certified_graph_case record005 29 28845201981440 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11963 14

certified_graph_case record006 29 28866766704672 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11964 14

certified_graph_case record007 29 28868824563840 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11965 14

certified_graph_case record008 29 28868958765184 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11966 14

theorem record009_parameters : Parameters record009 (rowOfCode 29) 28868964519936 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 28868964519936 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11967 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 28868964519936
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.small_allowed record009 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch119.candidate11967_checked

theorem record009_result : Result (29, 28868964519936) :=
  of_direct_small 29 28868964519936 (by decide) ⟨record009, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00200.record009.direct_core, record009_parameters, record009_coverage⟩
#print axioms record009_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00200

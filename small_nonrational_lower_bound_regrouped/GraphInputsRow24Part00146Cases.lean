module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00146Checked
public import GraphInputsRow24Part00146Metadata
public import GraphInputsRow24Part00146Frames
public import GraphInputsRow24Part00146Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch101
public import GraphInputsRow24Part00146Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00146
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 32236682878976 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10188 14

certified_graph_case record001 24 32266097065984 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10189 14

certified_graph_case record002 24 32266105389056 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10190 14

certified_graph_case record003 24 32268107153664 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10191 14

certified_graph_case record004 24 32268425166848 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10192 14

certified_graph_case record005 24 32268894871552 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10193 14

certified_graph_case record006 24 32271042085376 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10194 14

certified_graph_case record007 24 32299321147392 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10195 14

theorem record008_parameters : Parameters record008 (rowOfCode 24) 32300394364928 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32300394364928 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10196 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 32300394364928
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch101.candidate10196_checked

theorem record008_result : Result (24, 32300394364928) :=
  of_direct_small 24 32300394364928 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00146.record008.direct_core, record008_parameters, record008_coverage⟩
#print axioms record008_result

certified_graph_case record009 24 32300402491648 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10197 14

certified_graph_case record010 24 32300856786944 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10198 14

certified_graph_case record011 24 32301979271744 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10199 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00146

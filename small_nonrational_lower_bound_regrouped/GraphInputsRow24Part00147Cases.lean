module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00147Checked
public import GraphInputsRow24Part00147Metadata
public import GraphInputsRow24Part00147Frames
public import GraphInputsRow24Part00147Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch102
public import GraphInputsRow24Part00147Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 32332597969152 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10200 14

theorem record001_parameters : Parameters record001 (rowOfCode 24) 32332606357504 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32332606357504 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10201 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 32332606357504
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch102.candidate10201_checked

theorem record001_result : Result (24, 32332606357504) :=
  of_direct_small 24 32332606357504 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00147.record001.direct_core, record001_parameters, record001_coverage⟩
#print axioms record001_result

certified_graph_case record002 24 32333118048320 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10202 14

certified_graph_case record003 24 32335198292032 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10203 14

certified_graph_case record004 24 32335214936640 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10204 14

certified_graph_case record005 24 32438986277120 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10205 14

certified_graph_case record006 24 32438994665472 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10206 14

certified_graph_case record007 24 32439217488128 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10207 14

certified_graph_case record008 24 32439386800384 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10208 14

certified_graph_case record009 24 32439391027200 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10209 14

certified_graph_case record010 24 32439485890816 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10210 14

certified_graph_case record011 24 32439497920512 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10211 14

certified_graph_case record012 24 32441264832768 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10212 14

certified_graph_case record013 24 32441273221120 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10213 14

certified_graph_case record014 24 32441297862912 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10214 14

certified_graph_case record015 24 32441533235456 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10215 14

certified_graph_case record016 24 32441537462272 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10216 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00147

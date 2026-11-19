module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00148Checked
public import GraphInputsRow24Part00148Metadata
public import GraphInputsRow24Part00148Frames
public import GraphInputsRow24Part00148Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch102
public import GraphInputsRow24Part00148Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00148
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 24) 32441544744960 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32441544744960 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10217 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 32441544744960
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch102.candidate10217_checked

theorem record000_result : Result (24, 32441544744960) :=
  of_direct_small 24 32441544744960 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00148.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 24 32441566265600 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10218 14

certified_graph_case record002 24 32441578295296 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10219 14

certified_graph_case record003 24 32441767567616 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10220 14

certified_graph_case record004 24 32442841305344 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10221 14

certified_graph_case record005 24 32454048514304 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10222 14

certified_graph_case record006 24 32454060544000 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10223 14

certified_graph_case record007 24 32454249816320 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10224 14

certified_graph_case record008 24 32454423355392 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10225 14

certified_graph_case record009 24 32454456905728 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10226 14

certified_graph_case record010 24 32455323554048 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10227 14

certified_graph_case record011 24 32457873690656 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10228 14

certified_graph_case record012 24 32473312461056 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10229 14

certified_graph_case record013 24 32474533527808 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10230 14

theorem record014_parameters : Parameters record014 (rowOfCode 24) 32474541916160 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record014_coverage : Coverage record014 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32474541916160 :=
  GraphCoverageDescriptions.coverage_of_checked record014 GraphCoverageDescriptions.GraphCoverageBatch102.candidate10231 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 32474541916160
    (by rfl) record014_cells_exact
    (GraphCoverageDescriptions.small_allowed record014 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch102.candidate10231_checked

theorem record014_result : Result (24, 32474541916160) :=
  of_direct_small 24 32474541916160 (by decide) ⟨record014, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00148.record014.direct_core, record014_parameters, record014_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00148

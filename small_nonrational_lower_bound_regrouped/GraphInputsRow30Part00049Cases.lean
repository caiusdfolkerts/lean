module
prelude
public meta import GraphCases
public import GraphInputsRow30Part00049Checked
public import GraphInputsRow30Part00049Metadata
public import GraphInputsRow30Part00049Frames
public import GraphInputsRow30Part00049Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch120
public import GraphInputsRow30Part00049Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 30 30241175375872 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12047 14

certified_graph_case record001 30 30241418907776 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12048 14

certified_graph_case record002 30 30241435422848 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12049 14

theorem record003_parameters : Parameters record003 (rowOfCode 30) 30241670303760 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 30241670303760 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12050 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 30241670303760
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch120.candidate12050_checked

theorem record003_result : Result (30, 30241670303760) :=
  of_direct_small 30 30241670303760 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00049.record003.direct_core, record003_parameters, record003_coverage⟩
#print axioms record003_result

certified_graph_case record004 30 30242240463616 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12051 14

certified_graph_case record005 30 30242508898944 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12052 14

certified_graph_case record006 30 30242743779856 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12053 14

certified_graph_case record007 30 30246537592832 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12054 14

certified_graph_case record008 30 30253917671552 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12055 14

certified_graph_case record009 30 30254152552464 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12056 14

certified_graph_case record010 30 30255226028560 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12057 14

certified_graph_case record011 30 30305583108096 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12058 14

certified_graph_case record012 30 30314416179216 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12059 14

certified_graph_case record013 30 30314432823824 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12060 14

certified_graph_case record014 30 30315363958784 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12061 14

certified_graph_case record015 30 30378589487104 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12062 14

certified_graph_case record016 30 30382615970048 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12063 14

certified_graph_case record017 30 30511603126272 GraphCoverageDescriptions.GraphCoverageBatch120.candidate12064 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00049

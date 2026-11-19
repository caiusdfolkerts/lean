module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00135Checked
public import GraphInputsRow24Part00135Metadata
public import GraphInputsRow24Part00135Frames
public import GraphInputsRow24Part00135Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch100
public import GraphInputsRow24Part00135Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 31579552677888 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10056 14

certified_graph_case record001 24 31585207386368 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10057 14

certified_graph_case record002 24 31585744257024 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10058 14

certified_graph_case record003 24 31585752580096 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10059 14

certified_graph_case record004 24 31585793802240 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10060 14

certified_graph_case record005 24 31587337175296 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10061 14

certified_graph_case record006 24 31593797288192 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10062 14

certified_graph_case record007 24 31594115301376 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10063 14

certified_graph_case record008 24 31594338320384 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10064 14

certified_graph_case record009 24 31594585006080 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10065 14

certified_graph_case record010 24 31595927077120 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10066 14

certified_graph_case record011 24 31596732219904 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10067 14

certified_graph_case record012 24 31602369503488 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10068 14

theorem record013_parameters : Parameters record013 (rowOfCode 24) 31604517044224 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record013_coverage : Coverage record013 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31604517044224 :=
  GraphCoverageDescriptions.coverage_of_checked record013 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10069 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 31604517044224
    (by rfl) record013_cells_exact
    (GraphCoverageDescriptions.small_allowed record013 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch100.candidate10069_checked

theorem record013_result : Result (24, 31604517044224) :=
  of_direct_small 24 31604517044224 (by decide) ⟨record013, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00135.record013.direct_core, record013_parameters, record013_coverage⟩
#print axioms record013_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00135

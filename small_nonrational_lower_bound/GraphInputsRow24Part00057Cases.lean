module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00057Checked
public import GraphInputsRow24Part00057Metadata
public import GraphInputsRow24Part00057Frames
public import GraphInputsRow24Part00057Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch083
public import GraphInputsRow24Part00057Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 20930862547200 GraphCoverageDescriptions.GraphCoverageBatch083.candidate08322 14

certified_graph_case record001 24 20930862612480 GraphCoverageDescriptions.GraphCoverageBatch083.candidate08323 14

certified_graph_case record002 24 20935157498112 GraphCoverageDescriptions.GraphCoverageBatch083.candidate08324 14

certified_graph_case record003 24 20935157563392 GraphCoverageDescriptions.GraphCoverageBatch083.candidate08325 14

certified_graph_case record004 24 20938378711296 GraphCoverageDescriptions.GraphCoverageBatch083.candidate08326 14

certified_graph_case record005 24 20938649243712 GraphCoverageDescriptions.GraphCoverageBatch083.candidate08327 14

certified_graph_case record006 24 20969714434048 GraphCoverageDescriptions.GraphCoverageBatch083.candidate08328 14

certified_graph_case record007 24 21007368716289 GraphCoverageDescriptions.GraphCoverageBatch083.candidate08329 14

certified_graph_case record008 24 21035015475456 GraphCoverageDescriptions.GraphCoverageBatch083.candidate08330 14

certified_graph_case record009 24 21046621192192 GraphCoverageDescriptions.GraphCoverageBatch083.candidate08331 14

certified_graph_case record010 24 21046826639424 GraphCoverageDescriptions.GraphCoverageBatch083.candidate08332 14

certified_graph_case record011 24 21047900377152 GraphCoverageDescriptions.GraphCoverageBatch083.candidate08333 14

certified_graph_case record012 24 21076086095873 GraphCoverageDescriptions.GraphCoverageBatch083.candidate08334 14

theorem record013_parameters : Parameters record013 (rowOfCode 24) 21111452467200 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record013_coverage : Coverage record013 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 21111452467200 :=
  GraphCoverageDescriptions.coverage_of_checked record013 GraphCoverageDescriptions.GraphCoverageBatch083.candidate08335 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 21111452467200
    (by rfl) record013_cells_exact
    (GraphCoverageDescriptions.small_allowed record013 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch083.candidate08335_checked

theorem record013_result : Result (24, 21111452467200) :=
  of_direct_small 24 21111452467200 (by decide) ⟨record013, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00057.record013.direct_core, record013_parameters, record013_coverage⟩
#print axioms record013_result

certified_graph_case record014 24 21119497175296 GraphCoverageDescriptions.GraphCoverageBatch083.candidate08336 14

certified_graph_case record015 24 21119633522688 GraphCoverageDescriptions.GraphCoverageBatch083.candidate08337 14

certified_graph_case record016 24 21119641845760 GraphCoverageDescriptions.GraphCoverageBatch083.candidate08338 14

certified_graph_case record017 24 21119765643264 GraphCoverageDescriptions.GraphCoverageBatch083.candidate08339 14

certified_graph_case record018 24 21119773966336 GraphCoverageDescriptions.GraphCoverageBatch083.candidate08340 14

certified_graph_case record019 24 21120234307584 GraphCoverageDescriptions.GraphCoverageBatch083.candidate08341 14

certified_graph_case record020 24 21123934715904 GraphCoverageDescriptions.GraphCoverageBatch083.candidate08342 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00057

module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00005Checked
public import GraphInputsRow24Part00005Metadata
public import GraphInputsRow24Part00005Frames
public import GraphInputsRow24Part00005Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch063
public import GraphInputsRow24Part00005Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00005
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 3157606269568 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06376 14

certified_graph_case record001 24 3164726165760 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06377 14

certified_graph_case record002 24 3164730327296 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06378 14

certified_graph_case record003 24 3164730392576 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06379 14

certified_graph_case record004 24 3164998762624 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06380 14

certified_graph_case record005 24 3165000843392 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06381 14

certified_graph_case record006 24 3166678646784 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06382 14

certified_graph_case record007 24 3166806540544 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06383 14

certified_graph_case record008 24 3166810702080 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06384 14

certified_graph_case record009 24 3166810767360 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06385 14

certified_graph_case record010 24 3166876762368 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06386 14

certified_graph_case record011 24 3166876827648 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06387 14

certified_graph_case record012 24 3167079137408 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06388 14

certified_graph_case record013 24 3167081218176 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06389 14

certified_graph_case record014 24 3167850954752 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06390 14

certified_graph_case record015 24 3174392471552 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06391 14

certified_graph_case record016 24 3188151320576 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06392 14

certified_graph_case record017 24 3191263494400 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06393 14

certified_graph_case record018 24 3191267721216 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06394 14

certified_graph_case record019 24 3191271882752 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06395 14

theorem record020_parameters : Parameters record020 (rowOfCode 24) 3191333781504 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record020_coverage : Coverage record020 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 3191333781504 :=
  GraphCoverageDescriptions.coverage_of_checked record020 GraphCoverageDescriptions.GraphCoverageBatch063.candidate06396 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 3191333781504
    (by rfl) record020_cells_exact
    (GraphCoverageDescriptions.small_allowed record020 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch063.candidate06396_checked

theorem record020_result : Result (24, 3191333781504) :=
  of_direct_small 24 3191333781504 (by decide) ⟨record020, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00005.record020.direct_core, record020_parameters, record020_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00005

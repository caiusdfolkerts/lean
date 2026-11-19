module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00094Checked
public import GraphInputsRow31Part00094Metadata
public import GraphInputsRow31Part00094Frames
public import GraphInputsRow31Part00094Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch164
public import GraphInputsRow31Part00094Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00094
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 31) 18710528008256 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 18710528008256 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16406 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 18710528008256
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch164.candidate16406_checked

theorem record000_result : Result (31, 18710528008256) :=
  of_direct_small 31 18710528008256 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00094.record000.direct_core, record000_parameters, record000_coverage⟩

certified_graph_case record001 31 18769569652800 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16407 14

certified_graph_case record002 31 18778155393088 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16408 14

certified_graph_case record003 31 18779477131520 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16409 14

theorem record004_parameters : Parameters record004 (rowOfCode 31) 18801894686720 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 18801894686720 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16410 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 18801894686720
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch164.candidate16410_checked

theorem record004_result : Result (31, 18801894686720) :=
  of_direct_small 31 18801894686720 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00094.record004.direct_core, record004_parameters, record004_coverage⟩

certified_graph_case record005 31 18885654872064 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16411 14

certified_graph_case record006 31 18985635561536 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16412 14

certified_graph_case record007 31 18988856254528 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16413 14

certified_graph_case record008 31 19014503890944 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16414 14

certified_graph_case record009 31 19023215460928 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16415 14

certified_graph_case record010 31 19027512541184 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16416 14

certified_graph_case record011 31 19057442062336 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16417 14

certified_graph_case record012 31 19061871230976 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16418 14

certified_graph_case record013 31 19129853559040 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16419 14

certified_graph_case record014 31 19281857282048 GraphCoverageDescriptions.GraphCoverageBatch164.candidate16420 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00094

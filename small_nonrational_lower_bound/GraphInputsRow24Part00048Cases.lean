module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00048Checked
public import GraphInputsRow24Part00048Metadata
public import GraphInputsRow24Part00048Frames
public import GraphInputsRow24Part00048Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch080
public import GraphInputsRow24Part00048Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 19512581816320 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08053 14

certified_graph_case record001 24 19534926921728 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08054 14

certified_graph_case record002 24 19538991153152 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08055 14

theorem record003_parameters : Parameters record003 (rowOfCode 24) 19539090243584 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 19539090243584 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08056 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 19539090243584
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch080.candidate08056_checked

theorem record003_result : Result (24, 19539090243584) :=
  of_direct_small 24 19539090243584 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00048.record003.direct_core, record003_parameters, record003_coverage⟩
#print axioms record003_result

certified_graph_case record004 24 19564259704833 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08057 14

certified_graph_case record005 24 19573374091520 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08058 14

certified_graph_case record006 24 19573382479872 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08059 14

certified_graph_case record007 24 19573910798976 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08060 14

certified_graph_case record008 24 19586219016448 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08061 14

certified_graph_case record009 24 19586739079296 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08062 14

certified_graph_case record010 24 19587358294272 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08063 14

certified_graph_case record011 24 19587754656000 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08064 14

certified_graph_case record012 24 19587779266688 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08065 14

certified_graph_case record013 24 19588679008512 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08066 14

theorem record014_parameters : Parameters record014 (rowOfCode 24) 19588687396864 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record014_coverage : Coverage record014 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 19588687396864 :=
  GraphCoverageDescriptions.coverage_of_checked record014 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08067 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 19588687396864
    (by rfl) record014_cells_exact
    (GraphCoverageDescriptions.small_allowed record014 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch080.candidate08067_checked

theorem record014_result : Result (24, 19588687396864) :=
  of_direct_small 24 19588687396864 (by decide) ⟨record014, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00048.record014.direct_core, record014_parameters, record014_coverage⟩
#print axioms record014_result

certified_graph_case record015 24 19589079531776 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08068 14

certified_graph_case record016 24 19589090000896 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08069 14

certified_graph_case record017 24 19590759383296 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08070 14

certified_graph_case record018 24 19590767771648 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08071 14

certified_graph_case record019 24 19595052253440 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08072 14

certified_graph_case record020 24 19595060641792 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08073 14

certified_graph_case record021 24 19595320656128 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08074 14

certified_graph_case record022 24 19595324882944 GraphCoverageDescriptions.GraphCoverageBatch080.candidate08075 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00048

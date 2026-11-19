module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00046Checked
public import GraphInputsRow31Part00046Metadata
public import GraphInputsRow31Part00046Frames
public import GraphInputsRow31Part00046Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch159
public import GraphInputsRow31Part00046Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00046
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 8943540650240 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15985 14

certified_graph_case record001 31 8952126390528 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15986 14

certified_graph_case record002 31 8952399020160 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15987 14

certified_graph_case record003 31 8979042336768 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15988 14

certified_graph_case record004 31 8987628077056 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15989 14

certified_graph_case record005 31 8988036972544 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15990 14

certified_graph_case record006 31 9015942717696 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15991 14

certified_graph_case record007 31 9125465456768 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15992 14

certified_graph_case record008 31 9424571793664 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15993 14

theorem record009_parameters : Parameters record009 (rowOfCode 31) 9424580182016 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 9424580182016 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15994 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 9424580182016
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.small_allowed record009 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch159.candidate15994_checked

theorem record009_result : Result (31, 9424580182016) :=
  of_direct_small 31 9424580182016 (by decide) ⟨record009, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00046.record009.direct_core, record009_parameters, record009_coverage⟩

certified_graph_case record010 31 9475515744256 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15995 14

theorem record011_parameters : Parameters record011 (rowOfCode 31) 9493297561600 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record011_coverage : Coverage record011 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 9493297561600 :=
  GraphCoverageDescriptions.coverage_of_checked record011 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15996 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 9493297561600
    (by rfl) record011_cells_exact
    (GraphCoverageDescriptions.small_allowed record011 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch159.candidate15996_checked

theorem record011_result : Result (31, 9493297561600) :=
  of_direct_small 31 9493297561600 (by decide) ⟨record011, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00046.record011.direct_core, record011_parameters, record011_coverage⟩

theorem record012_parameters : Parameters record012 (rowOfCode 31) 9494601990144 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record012_coverage : Coverage record012 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 9494601990144 :=
  GraphCoverageDescriptions.coverage_of_checked record012 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15997 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 9494601990144
    (by rfl) record012_cells_exact
    (GraphCoverageDescriptions.small_allowed record012 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch159.candidate15997_checked

theorem record012_result : Result (31, 9494601990144) :=
  of_direct_small 31 9494601990144 (by decide) ⟨record012, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00046.record012.direct_core, record012_parameters, record012_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00046

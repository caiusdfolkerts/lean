module
prelude
public meta import GraphCases
public import GraphInputsRow16Part00039Checked
public import GraphInputsRow16Part00039Metadata
public import GraphInputsRow16Part00039Frames
public import GraphInputsRow16Part00039Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch020
public import GraphInputsRow16Part00039Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 16 34674630524928 GraphCoverageDescriptions.GraphCoverageBatch020.candidate02084 14

certified_graph_case record001 16 34674638848000 GraphCoverageDescriptions.GraphCoverageBatch020.candidate02085 14

certified_graph_case record002 16 34674671878144 GraphCoverageDescriptions.GraphCoverageBatch020.candidate02086 14

theorem record003_parameters : Parameters record003 (rowOfCode 16) 34675150295040 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34675150295040 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch020.candidate02087 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 34675150295040
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch020.candidate02087_checked

theorem record003_result : Result (16, 34675150295040) :=
  of_direct_small 16 34675150295040 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00039.record003.direct_core, record003_parameters, record003_coverage⟩
#print axioms record003_result

theorem record004_parameters : Parameters record004 (rowOfCode 16) 34675167330304 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34675167330304 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch020.candidate02088 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 34675167330304
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch020.candidate02088_checked

theorem record004_result : Result (16, 34675167330304) :=
  of_direct_small 16 34675167330304 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00039.record004.direct_core, record004_parameters, record004_coverage⟩
#print axioms record004_result

certified_graph_case record005 16 34681911836672 GraphCoverageDescriptions.GraphCoverageBatch020.candidate02089 14

certified_graph_case record006 16 34681920159744 GraphCoverageDescriptions.GraphCoverageBatch020.candidate02090 14

certified_graph_case record007 16 34682415091712 GraphCoverageDescriptions.GraphCoverageBatch020.candidate02091 14

certified_graph_case record008 16 34682431606784 GraphCoverageDescriptions.GraphCoverageBatch020.candidate02092 14

certified_graph_case record009 16 34682968408064 GraphCoverageDescriptions.GraphCoverageBatch020.candidate02093 14

certified_graph_case record010 16 34682976731136 GraphCoverageDescriptions.GraphCoverageBatch020.candidate02094 14

theorem record011_parameters : Parameters record011 (rowOfCode 16) 34683471663104 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record011_coverage : Coverage record011 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34683471663104 :=
  GraphCoverageDescriptions.coverage_of_checked record011 GraphCoverageDescriptions.GraphCoverageBatch020.candidate02095 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 34683471663104
    (by rfl) record011_cells_exact
    (GraphCoverageDescriptions.small_allowed record011 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch020.candidate02095_checked

theorem record011_result : Result (16, 34683471663104) :=
  of_direct_small 16 34683471663104 (by decide) ⟨record011, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00039.record011.direct_core, record011_parameters, record011_coverage⟩
#print axioms record011_result

certified_graph_case record012 16 34683505082880 GraphCoverageDescriptions.GraphCoverageBatch020.candidate02096 14

theorem record013_parameters : Parameters record013 (rowOfCode 16) 34763482726400 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record013_coverage : Coverage record013 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34763482726400 :=
  GraphCoverageDescriptions.coverage_of_checked record013 GraphCoverageDescriptions.GraphCoverageBatch020.candidate02097 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 34763482726400
    (by rfl) record013_cells_exact
    (GraphCoverageDescriptions.small_allowed record013 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch020.candidate02097_checked

theorem record013_result : Result (16, 34763482726400) :=
  of_direct_small 16 34763482726400 (by decide) ⟨record013, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00039.record013.direct_core, record013_parameters, record013_coverage⟩
#print axioms record013_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00039

module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00199Checked
public import GraphInputsRow29Part00199Metadata
public import GraphInputsRow29Part00199Frames
public import GraphInputsRow29Part00199Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch119
public import GraphCoverageBatch153
public import GraphInputsRow29Part00199Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00199
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 28708704387200 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11953 14

certified_graph_case record001 29 28717294321664 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11954 14

theorem record002_parameters : Parameters record002 (rowOfCode 29) 28717430603776 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 28717430603776 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11955 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 28717430603776
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch119.candidate11955_checked

theorem record002_result : Result (29, 28717430603776) :=
  of_direct_small 29 28717430603776 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00199.record002.direct_core, record002_parameters, record002_coverage⟩

certified_graph_case record003 29 28729196159104 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15386 14

certified_graph_case record004 29 28743199391744 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11956 14

certified_graph_case record005 29 28770243248128 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15387 14

theorem record006_parameters : Parameters record006 (rowOfCode 29) 28781855113216 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 28781855113216 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11957 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 28781855113216
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch119.candidate11957_checked

theorem record006_result : Result (29, 28781855113216) :=
  of_direct_small 29 28781855113216 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00199.record006.direct_core, record006_parameters, record006_coverage⟩

theorem record007_parameters : Parameters record007 (rowOfCode 29) 28797288087552 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 28797288087552 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11958 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 28797288087552
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch119.candidate11958_checked

theorem record007_result : Result (29, 28797288087552) :=
  of_direct_small 29 28797288087552 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00199.record007.direct_core, record007_parameters, record007_coverage⟩

certified_graph_case record008 29 28830123229184 GraphCoverageDescriptions.GraphCoverageBatch153.candidate15388 14

theorem record009_parameters : Parameters record009 (rowOfCode 29) 28830131552256 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 28830131552256 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch119.candidate11959 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 28830131552256
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.small_allowed record009 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch119.candidate11959_checked

theorem record009_result : Result (29, 28830131552256) :=
  of_direct_small 29 28830131552256 (by decide) ⟨record009, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00199.record009.direct_core, record009_parameters, record009_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00199

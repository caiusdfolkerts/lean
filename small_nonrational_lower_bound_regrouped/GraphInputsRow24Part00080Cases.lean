module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00080Checked
public import GraphInputsRow24Part00080Metadata
public import GraphInputsRow24Part00080Frames
public import GraphInputsRow24Part00080Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch089
public import GraphInputsRow24Part00080Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 24) 24432324444416 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24432324444416 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08956 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24432324444416
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch089.candidate08956_checked

theorem record000_result : Result (24, 24432324444416) :=
  of_direct_small 24 24432324444416 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00080.record000.direct_core, record000_parameters, record000_coverage⟩
#print axioms record000_result

certified_graph_case record001 24 24432477241600 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08957 14

certified_graph_case record002 24 24432481468416 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08958 14

certified_graph_case record003 24 24432487710720 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08959 14

certified_graph_case record004 24 24432592847104 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08960 14

certified_graph_case record005 24 24432605136896 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08961 14

certified_graph_case record006 24 24432727048448 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08962 14

certified_graph_case record007 24 24436891779072 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08963 14

certified_graph_case record008 24 24437021737728 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08964 14

certified_graph_case record009 24 24438565568768 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08965 14

certified_graph_case record010 24 24438918627584 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08966 14

certified_graph_case record011 24 24438920773632 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08967 14

certified_graph_case record012 24 24438927015936 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08968 14

theorem record013_parameters : Parameters record013 (rowOfCode 24) 24438968172800 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record013_coverage : Coverage record013 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24438968172800 :=
  GraphCoverageDescriptions.coverage_of_checked record013 GraphCoverageDescriptions.GraphCoverageBatch089.candidate08969 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24438968172800
    (by rfl) record013_cells_exact
    (GraphCoverageDescriptions.small_allowed record013 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch089.candidate08969_checked

theorem record013_result : Result (24, 24438968172800) :=
  of_direct_small 24 24438968172800 (by decide) ⟨record013, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00080.record013.direct_core, record013_parameters, record013_coverage⟩
#print axioms record013_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00080

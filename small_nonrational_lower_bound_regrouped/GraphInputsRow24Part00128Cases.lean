module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00128Checked
public import GraphInputsRow24Part00128Metadata
public import GraphInputsRow24Part00128Frames
public import GraphInputsRow24Part00128Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch099
public import GraphInputsRow24Part00128Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 31414809591808 GraphCoverageDescriptions.GraphCoverageBatch099.candidate09955 14

certified_graph_case record001 24 31415069606144 GraphCoverageDescriptions.GraphCoverageBatch099.candidate09956 14

certified_graph_case record002 24 31415081107457 GraphCoverageDescriptions.GraphCoverageBatch099.candidate09957 14

theorem record003_parameters : Parameters record003 (rowOfCode 24) 31415081115648 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31415081115648 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch099.candidate09958 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 31415081115648
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch099.candidate09958_checked

theorem record003_result : Result (24, 31415081115648) :=
  of_direct_small 24 31415081115648 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00128.record003.direct_core, record003_parameters, record003_coverage⟩
#print axioms record003_result

certified_graph_case record004 24 31415270908160 GraphCoverageDescriptions.GraphCoverageBatch099.candidate09959 14

certified_graph_case record005 24 31415874420992 GraphCoverageDescriptions.GraphCoverageBatch099.candidate09960 14

certified_graph_case record006 24 31416142823680 GraphCoverageDescriptions.GraphCoverageBatch099.candidate09961 14

theorem record007_parameters : Parameters record007 (rowOfCode 24) 31416154853376 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31416154853376 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch099.candidate09962 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 31416154853376
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch099.candidate09962_checked

theorem record007_result : Result (24, 31416154853376) :=
  of_direct_small 24 31416154853376 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00128.record007.direct_core, record007_parameters, record007_coverage⟩
#print axioms record007_result

theorem record008_parameters : Parameters record008 (rowOfCode 24) 31416344125696 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31416344125696 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch099.candidate09963 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 31416344125696
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch099.candidate09963_checked

theorem record008_result : Result (24, 31416344125696) :=
  of_direct_small 24 31416344125696 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00128.record008.direct_core, record008_parameters, record008_coverage⟩
#print axioms record008_result

certified_graph_case record009 24 31423395332096 GraphCoverageDescriptions.GraphCoverageBatch099.candidate09964 14

certified_graph_case record010 24 31431376511008 GraphCoverageDescriptions.GraphCoverageBatch099.candidate09965 14

certified_graph_case record011 24 31442654527744 GraphCoverageDescriptions.GraphCoverageBatch099.candidate09966 14

certified_graph_case record012 24 31443191398400 GraphCoverageDescriptions.GraphCoverageBatch099.candidate09967 14

certified_graph_case record013 24 31443199721472 GraphCoverageDescriptions.GraphCoverageBatch099.candidate09968 14

certified_graph_case record014 24 31448316772353 GraphCoverageDescriptions.GraphCoverageBatch099.candidate09969 14

certified_graph_case record015 24 31448895652096 GraphCoverageDescriptions.GraphCoverageBatch099.candidate09970 14

certified_graph_case record016 24 31449168281600 GraphCoverageDescriptions.GraphCoverageBatch099.candidate09971 14

certified_graph_case record017 24 31449432522752 GraphCoverageDescriptions.GraphCoverageBatch099.candidate09972 14

certified_graph_case record018 24 31449440845824 GraphCoverageDescriptions.GraphCoverageBatch099.candidate09973 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128

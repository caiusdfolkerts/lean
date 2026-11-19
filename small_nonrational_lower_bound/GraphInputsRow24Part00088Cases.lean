module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00088Checked
public import GraphInputsRow24Part00088Metadata
public import GraphInputsRow24Part00088Frames
public import GraphInputsRow24Part00088Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch090
public import GraphInputsRow24Part00088Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 24) 24645193703488 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24645193703488 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09075 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24645193703488
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch090.candidate09075_checked

theorem record000_result : Result (24, 24645193703488) :=
  of_direct_small 24 24645193703488 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record000.direct_core, record000_parameters, record000_coverage⟩
#print axioms record000_result

certified_graph_case record001 24 24647340917312 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09076 14

certified_graph_case record002 24 24663849844800 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09077 14

theorem record003_parameters : Parameters record003 (rowOfCode 24) 24663984062464 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24663984062464 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09078 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24663984062464
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch090.candidate09078_checked

theorem record003_result : Result (24, 24663984062464) :=
  of_direct_small 24 24663984062464 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record003.direct_core, record003_parameters, record003_coverage⟩
#print axioms record003_result

certified_graph_case record004 24 24663986143232 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09079 14

theorem record005_parameters : Parameters record005 (rowOfCode 24) 24665997320256 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24665997320256 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09080 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24665997320256
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch090.candidate09080_checked

theorem record005_result : Result (24, 24665997320256) :=
  of_direct_small 24 24665997320256 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record005.direct_core, record005_parameters, record005_coverage⟩
#print axioms record005_result

certified_graph_case record006 24 24666064437248 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09081 14

certified_graph_case record007 24 24666066518016 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09082 14

theorem record008_parameters : Parameters record008 (rowOfCode 24) 24666198508032 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24666198508032 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09083 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24666198508032
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch090.candidate09083_checked

theorem record008_result : Result (24, 24666198508032) :=
  of_direct_small 24 24666198508032 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00088.record008.direct_core, record008_parameters, record008_coverage⟩
#print axioms record008_result

certified_graph_case record009 24 24672536117248 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09084 14

certified_graph_case record010 24 24672734298112 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09085 14

certified_graph_case record011 24 24672775454976 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09086 14

certified_graph_case record012 24 24676940185600 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09087 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00088

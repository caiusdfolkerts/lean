module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00040Checked
public import GraphInputsRow24Part00040Metadata
public import GraphInputsRow24Part00040Frames
public import GraphInputsRow24Part00040Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch077
public import GraphInputsRow24Part00040Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 17470349901824 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07787 14

certified_graph_case record001 24 17489125736704 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07788 14

theorem record002_parameters : Parameters record002 (rowOfCode 24) 17493422833664 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 17493422833664 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07789 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 17493422833664
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch077.candidate07789_checked

theorem record002_result : Result (24, 17493422833664) :=
  of_direct_small 24 17493422833664 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00040.record002.direct_core, record002_parameters, record002_coverage⟩

theorem record003_parameters : Parameters record003 (rowOfCode 24) 17493695397888 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 17493695397888 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07790 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 17493695397888
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch077.candidate07790_checked

theorem record003_result : Result (24, 17493695397888) :=
  of_direct_small 24 17493695397888 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00040.record003.direct_core, record003_parameters, record003_coverage⟩

certified_graph_case record004 24 17494207365120 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07791 14

theorem record005_parameters : Parameters record005 (rowOfCode 24) 17498368114688 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record005_coverage : Coverage record005 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 17498368114688 :=
  GraphCoverageDescriptions.coverage_of_checked record005 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07792 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 17498368114688
    (by rfl) record005_cells_exact
    (GraphCoverageDescriptions.small_allowed record005 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch077.candidate07792_checked

theorem record005_result : Result (24, 17498368114688) :=
  of_direct_small 24 17498368114688 (by decide) ⟨record005, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00040.record005.direct_core, record005_parameters, record005_coverage⟩

theorem record006_parameters : Parameters record006 (rowOfCode 24) 17501991927808 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record006_coverage : Coverage record006 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 17501991927808 :=
  GraphCoverageDescriptions.coverage_of_checked record006 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07793 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 17501991927808
    (by rfl) record006_cells_exact
    (GraphCoverageDescriptions.small_allowed record006 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch077.candidate07793_checked

theorem record006_result : Result (24, 17501991927808) :=
  of_direct_small 24 17501991927808 (by decide) ⟨record006, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00040.record006.direct_core, record006_parameters, record006_coverage⟩

certified_graph_case record007 24 17519171731456 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07794 14

certified_graph_case record008 24 17523483640064 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07795 14

certified_graph_case record009 24 17523752108032 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07796 14

certified_graph_case record010 24 17523760431104 GraphCoverageDescriptions.GraphCoverageBatch077.candidate07797 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040

module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00141Checked
public import GraphInputsRow24Part00141Metadata
public import GraphInputsRow24Part00141Frames
public import GraphInputsRow24Part00141Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch101
public import GraphInputsRow24Part00141Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00141
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 31929349967936 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10138 14

certified_graph_case record001 24 31961603670272 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10139 14

certified_graph_case record002 24 31973012701440 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10140 14

certified_graph_case record003 24 31994356498688 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10141 14

certified_graph_case record004 24 31994629128192 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10142 14

certified_graph_case record005 24 31994901692416 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10143 14

certified_graph_case record006 24 31995091550208 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10144 14

theorem record007_parameters : Parameters record007 (rowOfCode 24) 32011536367616 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32011536367616 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10145 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 32011536367616
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch101.candidate10145_checked

theorem record007_result : Result (24, 32011536367616) :=
  of_direct_small 24 32011536367616 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00141.record007.direct_core, record007_parameters, record007_coverage⟩

certified_graph_case record008 24 32011808931840 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10146 14

theorem record009_parameters : Parameters record009 (rowOfCode 24) 32012271353856 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32012271353856 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10147 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 32012271353856
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.small_allowed record009 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch101.candidate10147_checked

theorem record009_result : Result (24, 32012271353856) :=
  of_direct_small 24 32012271353856 (by decide) ⟨record009, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00141.record009.direct_core, record009_parameters, record009_coverage⟩

theorem record010_parameters : Parameters record010 (rowOfCode 24) 32012337414144 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record010_coverage : Coverage record010 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32012337414144 :=
  GraphCoverageDescriptions.coverage_of_checked record010 GraphCoverageDescriptions.GraphCoverageBatch101.candidate10148 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 32012337414144
    (by rfl) record010_cells_exact
    (GraphCoverageDescriptions.small_allowed record010 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch101.candidate10148_checked

theorem record010_result : Result (24, 32012337414144) :=
  of_direct_small 24 32012337414144 (by decide) ⟨record010, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00141.record010.direct_core, record010_parameters, record010_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00141

module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00032Checked
public import GraphInputsRow24Part00032Metadata
public import GraphInputsRow24Part00032Frames
public import GraphInputsRow24Part00032Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch076
public import GraphInputsRow24Part00032Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00032
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 16712867053568 GraphCoverageDescriptions.GraphCoverageBatch076.candidate07613 14

certified_graph_case record001 24 16713403858944 GraphCoverageDescriptions.GraphCoverageBatch076.candidate07614 14

theorem record002_parameters : Parameters record002 (rowOfCode 24) 16717155696896 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 16717155696896 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch076.candidate07615 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 16717155696896
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch076.candidate07615_checked

theorem record002_result : Result (24, 16717155696896) :=
  of_direct_small 24 16717155696896 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00032.record002.direct_core, record002_parameters, record002_coverage⟩

theorem record003_parameters : Parameters record003 (rowOfCode 24) 16717490225152 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record003_coverage : Coverage record003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 16717490225152 :=
  GraphCoverageDescriptions.coverage_of_checked record003 GraphCoverageDescriptions.GraphCoverageBatch076.candidate07616 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 16717490225152
    (by rfl) record003_cells_exact
    (GraphCoverageDescriptions.small_allowed record003 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch076.candidate07616_checked

theorem record003_result : Result (24, 16717490225152) :=
  of_direct_small 24 16717490225152 (by decide) ⟨record003, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00032.record003.direct_core, record003_parameters, record003_coverage⟩

theorem record004_parameters : Parameters record004 (rowOfCode 24) 16721452793856 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 16721452793856 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch076.candidate07617 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 16721452793856
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch076.candidate07617_checked

theorem record004_result : Result (24, 16721452793856) :=
  of_direct_small 24 16721452793856 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00032.record004.direct_core, record004_parameters, record004_coverage⟩

certified_graph_case record005 24 16721725358080 GraphCoverageDescriptions.GraphCoverageBatch076.candidate07618 14

certified_graph_case record006 24 16722187780096 GraphCoverageDescriptions.GraphCoverageBatch076.candidate07619 14

certified_graph_case record007 24 16729469091840 GraphCoverageDescriptions.GraphCoverageBatch076.candidate07620 14

certified_graph_case record008 24 16735478546688 GraphCoverageDescriptions.GraphCoverageBatch076.candidate07621 14

certified_graph_case record009 24 16739911925760 GraphCoverageDescriptions.GraphCoverageBatch076.candidate07622 14

certified_graph_case record010 24 16740448731136 GraphCoverageDescriptions.GraphCoverageBatch076.candidate07623 14

certified_graph_case record011 24 16744609480704 GraphCoverageDescriptions.GraphCoverageBatch076.candidate07624 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00032

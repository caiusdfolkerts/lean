module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00087Checked
public import GraphInputsRow24Part00087Metadata
public import GraphInputsRow24Part00087Frames
public import GraphInputsRow24Part00087Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch090
public import GraphInputsRow24Part00087Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 24 24640513655040 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09061 14

certified_graph_case record001 24 24640515801088 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09062 14

theorem record002_parameters : Parameters record002 (rowOfCode 24) 24640522043392 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24640522043392 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09063 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24640522043392
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch090.candidate09063_checked

theorem record002_result : Result (24, 24640522043392) :=
  of_direct_small 24 24640522043392 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00087.record002.direct_core, record002_parameters, record002_coverage⟩
#print axioms record002_result

certified_graph_case record003 24 24640563200256 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09064 14

certified_graph_case record004 24 24640573409280 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09065 14

certified_graph_case record005 24 24640837650432 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09066 14

certified_graph_case record006 24 24641032953920 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09067 14

certified_graph_case record007 24 24642777514752 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09068 14

certified_graph_case record008 24 24643180167744 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09069 14

theorem record009_parameters : Parameters record009 (rowOfCode 24) 24644723949824 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record009_coverage : Coverage record009 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 24644723949824 :=
  GraphCoverageDescriptions.coverage_of_checked record009 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09070 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 24644723949824
    (by rfl) record009_cells_exact
    (GraphCoverageDescriptions.small_allowed record009 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch090.candidate09070_checked

theorem record009_result : Result (24, 24644723949824) :=
  of_direct_small 24 24644723949824 (by decide) ⟨record009, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00087.record009.direct_core, record009_parameters, record009_coverage⟩
#print axioms record009_result

certified_graph_case record010 24 24644734158848 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09071 14

certified_graph_case record011 24 24645077057600 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09072 14

certified_graph_case record012 24 24645079154688 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09073 14

certified_graph_case record013 24 24645126602816 GraphCoverageDescriptions.GraphCoverageBatch090.candidate09074 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00087

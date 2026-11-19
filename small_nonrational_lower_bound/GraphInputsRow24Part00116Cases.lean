module
prelude
public meta import GraphCases
public import GraphInputsRow24Part00116Checked
public import GraphInputsRow24Part00116Metadata
public import GraphInputsRow24Part00116Frames
public import GraphInputsRow24Part00116Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch096
public import GraphInputsRow24Part00116Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00116
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 24) 27939056926720 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 27939056926720 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch096.candidate09633 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 27939056926720
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch096.candidate09633_checked

theorem record000_result : Result (24, 27939056926720) :=
  of_direct_small 24 27939056926720 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00116.record000.direct_core, record000_parameters, record000_coverage⟩
#print axioms record000_result

certified_graph_case record001 24 27939098083584 GraphCoverageDescriptions.GraphCoverageBatch096.candidate09634 14

certified_graph_case record002 24 27941312398080 GraphCoverageDescriptions.GraphCoverageBatch096.candidate09635 14

certified_graph_case record003 24 27943258833152 GraphCoverageDescriptions.GraphCoverageBatch096.candidate09636 14

theorem record004_parameters : Parameters record004 (rowOfCode 24) 27943269042176 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record004_coverage : Coverage record004 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 27943269042176 :=
  GraphCoverageDescriptions.coverage_of_checked record004 GraphCoverageDescriptions.GraphCoverageBatch096.candidate09637 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 27943269042176
    (by rfl) record004_cells_exact
    (GraphCoverageDescriptions.small_allowed record004 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch096.candidate09637_checked

theorem record004_result : Result (24, 27943269042176) :=
  of_direct_small 24 27943269042176 (by decide) ⟨record004, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00116.record004.direct_core, record004_parameters, record004_coverage⟩
#print axioms record004_result

certified_graph_case record005 24 27943661486144 GraphCoverageDescriptions.GraphCoverageBatch096.candidate09638 14

certified_graph_case record006 24 27943728586816 GraphCoverageDescriptions.GraphCoverageBatch096.candidate09639 14

certified_graph_case record007 24 27971269181440 GraphCoverageDescriptions.GraphCoverageBatch096.candidate09640 14

certified_graph_case record008 24 27971310338304 GraphCoverageDescriptions.GraphCoverageBatch096.candidate09641 14

certified_graph_case record009 24 28041076080896 GraphCoverageDescriptions.GraphCoverageBatch096.candidate09642 14

certified_graph_case record010 24 28041080242432 GraphCoverageDescriptions.GraphCoverageBatch096.candidate09643 14

certified_graph_case record011 24 28041080307712 GraphCoverageDescriptions.GraphCoverageBatch096.candidate09644 14

certified_graph_case record012 24 28041082323200 GraphCoverageDescriptions.GraphCoverageBatch096.candidate09645 14

certified_graph_case record013 24 28047521628416 GraphCoverageDescriptions.GraphCoverageBatch096.candidate09646 14

certified_graph_case record014 24 28047785869568 GraphCoverageDescriptions.GraphCoverageBatch096.candidate09647 14

certified_graph_case record015 24 28047785934848 GraphCoverageDescriptions.GraphCoverageBatch096.candidate09648 14

certified_graph_case record016 24 28076495437824 GraphCoverageDescriptions.GraphCoverageBatch096.candidate09649 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00116

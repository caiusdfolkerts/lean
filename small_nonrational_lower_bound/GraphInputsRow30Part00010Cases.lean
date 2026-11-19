module
prelude
public meta import GraphCases
public import GraphInputsRow30Part00010Checked
public import GraphInputsRow30Part00010Metadata
public import GraphInputsRow30Part00010Frames
public import GraphInputsRow30Part00010Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch108
public import GraphCoverageBatch155
public import GraphInputsRow30Part00010Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00010
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 30 6637144342528 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10835 14

certified_graph_case record001 30 6637210337536 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10836 14

certified_graph_case record002 30 6644726501632 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15550 14

certified_graph_case record003 30 6674941788192 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10837 14

certified_graph_case record004 30 6707409321985 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10838 14

certified_graph_case record005 30 6711570071553 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10839 14

certified_graph_case record006 30 6727198113792 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10840 14

certified_graph_case record007 30 6727206436864 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10841 14

certified_graph_case record008 30 6752966836480 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10842 14

certified_graph_case record009 30 6791622623232 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10843 14

certified_graph_case record010 30 6791630946304 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10844 14

certified_graph_case record011 30 6807055532288 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10845 14

certified_graph_case record012 30 6823834877952 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10846 14

certified_graph_case record013 30 6839899062272 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10847 14

certified_graph_case record014 30 6840406802688 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10848 14

certified_graph_case record015 30 6840419092480 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10849 14

certified_graph_case record016 30 6844835693312 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10850 14

theorem record017_parameters : Parameters record017 (rowOfCode 30) 6851076817664 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record017_coverage : Coverage record017 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 6851076817664 :=
  GraphCoverageDescriptions.coverage_of_checked record017 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10851 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 6851076817664
    (by rfl) record017_cells_exact
    (GraphCoverageDescriptions.small_allowed record017 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch108.candidate10851_checked

theorem record017_result : Result (30, 6851076817664) :=
  of_direct_small 30 6851076817664 (by decide) ⟨record017, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00010.record017.direct_core, record017_parameters, record017_coverage⟩
#print axioms record017_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00010

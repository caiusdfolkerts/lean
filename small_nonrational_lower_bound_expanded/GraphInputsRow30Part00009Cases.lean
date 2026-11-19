module
prelude
public meta import GraphCases
public import GraphInputsRow30Part00009Checked
public import GraphInputsRow30Part00009Metadata
public import GraphInputsRow30Part00009Frames
public import GraphInputsRow30Part00009Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch108
public import GraphCoverageBatch155
public import GraphInputsRow30Part00009Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00009
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 30 6379377131520 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10815 14

certified_graph_case record001 30 6379905483264 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10816 14

certified_graph_case record002 30 6379913871360 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10817 14

certified_graph_case record003 30 6413204062208 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10818 14

certified_graph_case record004 30 6425565003776 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10819 14

certified_graph_case record005 30 6425825018112 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10820 14

certified_graph_case record006 30 6425837307904 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10821 14

certified_graph_case record007 30 6426076645632 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10822 14

certified_graph_case record008 30 6434398013696 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10823 14

certified_graph_case record009 30 6434406402048 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10824 14

theorem record010_parameters : Parameters record010 (rowOfCode 30) 6434414658304 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record010_coverage : Coverage record010 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 6434414658304 :=
  GraphCoverageDescriptions.coverage_of_checked record010 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10825 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 6434414658304
    (by rfl) record010_cells_exact
    (GraphCoverageDescriptions.small_allowed record010 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch108.candidate10825_checked

theorem record010_result : Result (30, 6434414658304) :=
  of_direct_small 30 6434414658304 (by decide) ⟨record010, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00009.record010.direct_core, record010_parameters, record010_coverage⟩

certified_graph_case record011 30 6442727901184 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10826 14

certified_graph_case record012 30 6443017175040 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10827 14

certified_graph_case record013 30 6443256250888 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10828 14

certified_graph_case record014 30 6451854573568 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10829 14

certified_graph_case record015 30 6516279083008 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10830 14

certified_graph_case record016 30 6524600582144 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10831 14

certified_graph_case record017 30 6602618929184 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10832 14

theorem record018_parameters : Parameters record018 (rowOfCode 30) 6603015290912 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record018_coverage : Coverage record018 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 6603015290912 :=
  GraphCoverageDescriptions.coverage_of_checked record018 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10833 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 6603015290912
    (by rfl) record018_cells_exact
    (GraphCoverageDescriptions.small_allowed record018 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch108.candidate10833_checked

theorem record018_result : Result (30, 6603015290912) :=
  of_direct_small 30 6603015290912 (by decide) ⟨record018, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00009.record018.direct_core, record018_parameters, record018_coverage⟩

certified_graph_case record019 30 6615900143648 GraphCoverageDescriptions.GraphCoverageBatch155.candidate15549 14

certified_graph_case record020 30 6637012221952 GraphCoverageDescriptions.GraphCoverageBatch108.candidate10834 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00009

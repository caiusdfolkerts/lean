module
prelude
public meta import GraphCases
public import GraphInputsRow26Part00068Checked
public import GraphInputsRow26Part00068Metadata
public import GraphInputsRow26Part00068Frames
public import GraphInputsRow26Part00068Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch100
public import GraphInputsRow26Part00068Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00068
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 26 31570266161152 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10050 14

theorem record001_parameters : Parameters record001 (rowOfCode 26) 31570728583168 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record001_coverage : Coverage record001 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31570728583168 :=
  GraphCoverageDescriptions.coverage_of_checked record001 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10051 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 31570728583168
    (by rfl) record001_cells_exact
    (GraphCoverageDescriptions.small_allowed record001 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch100.candidate10051_checked

theorem record001_result : Result (26, 31570728583168) :=
  of_direct_small 26 31570728583168 (by decide) ⟨record001, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00068.record001.direct_core, record001_parameters, record001_coverage⟩

certified_graph_case record002 26 31579304951808 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10054 14

certified_graph_case record003 26 31579313274880 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10055 14

certified_graph_case record004 26 31579552677888 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10056 14

certified_graph_case record005 26 31585744257024 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10058 14

certified_graph_case record006 26 31585752580096 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10059 14

certified_graph_case record007 26 31585793802240 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10060 14

certified_graph_case record008 26 31593797288192 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10062 14

certified_graph_case record009 26 31594115301376 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10063 14

certified_graph_case record010 26 31594338320384 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10064 14

theorem record011_parameters : Parameters record011 (rowOfCode 26) 31594585006080 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record011_coverage : Coverage record011 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31594585006080 :=
  GraphCoverageDescriptions.coverage_of_checked record011 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10065 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 31594585006080
    (by rfl) record011_cells_exact
    (GraphCoverageDescriptions.small_allowed record011 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch100.candidate10065_checked

theorem record011_result : Result (26, 31594585006080) :=
  of_direct_small 26 31594585006080 (by decide) ⟨record011, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00068.record011.direct_core, record011_parameters, record011_coverage⟩

certified_graph_case record012 26 31596732219904 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10067 14

certified_graph_case record013 26 31602369503488 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10068 14

certified_graph_case record014 26 31604517044224 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10069 14

certified_graph_case record015 26 31605053849600 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10070 14

certified_graph_case record016 26 31655386480640 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10073 14

certified_graph_case record017 26 31689679110144 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10075 14

certified_graph_case record018 26 31722914775040 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10076 14

certified_graph_case record019 26 31722964320256 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10077 14

theorem record020_parameters : Parameters record020 (rowOfCode 26) 31751688716544 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record020_coverage : Coverage record020 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 31751688716544 :=
  GraphCoverageDescriptions.coverage_of_checked record020 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10078 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 31751688716544
    (by rfl) record020_cells_exact
    (GraphCoverageDescriptions.small_allowed record020 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch100.candidate10078_checked

theorem record020_result : Result (26, 31751688716544) :=
  of_direct_small 26 31751688716544 (by decide) ⟨record020, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00068.record020.direct_core, record020_parameters, record020_coverage⟩

certified_graph_case record021 26 31751825063936 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10079 14

certified_graph_case record022 26 31751833387008 GraphCoverageDescriptions.GraphCoverageBatch100.candidate10080 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00068

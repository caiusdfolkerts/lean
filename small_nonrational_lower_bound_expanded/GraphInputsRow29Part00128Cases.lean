module
prelude
public meta import GraphCases
public import GraphInputsRow29Part00128Checked
public import GraphInputsRow29Part00128Metadata
public import GraphInputsRow29Part00128Frames
public import GraphInputsRow29Part00128Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch116
public import GraphCoverageBatch150
public import GraphInputsRow29Part00128Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00128
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 29 21522118934784 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15000 14

certified_graph_case record001 29 21522887016448 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11658 14

certified_graph_case record002 29 21527047442560 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11659 14

certified_graph_case record003 29 21528120918656 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11660 14

certified_graph_case record004 29 21535001706752 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15001 14

certified_graph_case record005 29 21535771869184 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11661 14

certified_graph_case record006 29 21587715752192 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15002 14

theorem record007_parameters : Parameters record007 (rowOfCode 29) 21588252622848 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 21588252622848 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15003 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 21588252622848
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch150.candidate15003_checked

theorem record007_result : Result (29, 21588252622848) :=
  of_direct_small 29 21588252622848 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00128.record007.direct_core, record007_parameters, record007_coverage⟩

certified_graph_case record008 29 21588260945920 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11662 14

certified_graph_case record009 29 21590836314368 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15004 14

theorem record010_parameters : Parameters record010 (rowOfCode 29) 21591472275456 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record010_coverage : Coverage record010 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 21591472275456 :=
  GraphCoverageDescriptions.coverage_of_checked record010 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11663 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 21591472275456
    (by rfl) record010_cells_exact
    (GraphCoverageDescriptions.small_allowed record010 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch116.candidate11663_checked

theorem record010_result : Result (29, 21591472275456) :=
  of_direct_small 29 21591472275456 (by decide) ⟨record010, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00128.record010.direct_core, record010_parameters, record010_coverage⟩

certified_graph_case record011 29 21596305654016 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15005 14

certified_graph_case record012 29 21596574121984 GraphCoverageDescriptions.GraphCoverageBatch150.candidate15006 14

theorem record013_parameters : Parameters record013 (rowOfCode 29) 21596582445056 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record013_coverage : Coverage record013 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 21596582445056 :=
  GraphCoverageDescriptions.coverage_of_checked record013 GraphCoverageDescriptions.GraphCoverageBatch116.candidate11664 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 21596582445056
    (by rfl) record013_cells_exact
    (GraphCoverageDescriptions.small_allowed record013 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch116.candidate11664_checked

theorem record013_result : Result (29, 21596582445056) :=
  of_direct_small 29 21596582445056 (by decide) ⟨record013, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00128.record013.direct_core, record013_parameters, record013_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00128

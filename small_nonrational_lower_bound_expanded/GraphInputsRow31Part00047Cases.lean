module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00047Checked
public import GraphInputsRow31Part00047Metadata
public import GraphInputsRow31Part00047Frames
public import GraphInputsRow31Part00047Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch159
public import GraphCoverageBatch160
public import GraphInputsRow31Part00047Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00047
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 9496978530560 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15998 14

certified_graph_case record001 31 9528523424000 GraphCoverageDescriptions.GraphCoverageBatch159.candidate15999 14

certified_graph_case record002 31 9531337736960 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16000 14

certified_graph_case record003 31 9539931930624 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16001 14

certified_graph_case record004 31 9539940253696 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16002 14

certified_graph_case record005 31 9578583490560 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16003 14

certified_graph_case record006 31 9668789272576 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16004 14

certified_graph_case record007 31 9677370851328 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16005 14

certified_graph_case record008 31 9715287359744 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16006 14

certified_graph_case record009 31 9716022411264 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16007 14

theorem record010_parameters : Parameters record010 (rowOfCode 31) 10010104954880 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record010_coverage : Coverage record010 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 10010104954880 :=
  GraphCoverageDescriptions.coverage_of_checked record010 GraphCoverageDescriptions.GraphCoverageBatch160.candidate16008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 10010104954880
    (by rfl) record010_cells_exact
    (GraphCoverageDescriptions.small_allowed record010 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch160.candidate16008_checked

theorem record010_result : Result (31, 10010104954880) :=
  of_direct_small 31 10010104954880 (by decide) ⟨record010, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00047.record010.direct_core, record010_parameters, record010_coverage⟩
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00047

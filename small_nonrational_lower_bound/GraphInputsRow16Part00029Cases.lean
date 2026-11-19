module
prelude
public meta import GraphCases
public import GraphInputsRow16Part00029Checked
public import GraphInputsRow16Part00029Metadata
public import GraphInputsRow16Part00029Frames
public import GraphInputsRow16Part00029Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch016
public import GraphCoverageBatch017
public import GraphInputsRow16Part00029Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

theorem record000_parameters : Parameters record000 (rowOfCode 16) 28153120555008 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record000_coverage : Coverage record000 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 28153120555008 :=
  GraphCoverageDescriptions.coverage_of_checked record000 GraphCoverageDescriptions.GraphCoverageBatch016.candidate01677 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 28153120555008
    (by rfl) record000_cells_exact
    (GraphCoverageDescriptions.small_allowed record000 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch016.candidate01677_checked

theorem record000_result : Result (16, 28153120555008) :=
  of_direct_small 16 28153120555008 (by decide) ⟨record000, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record000.direct_core, record000_parameters, record000_coverage⟩
#print axioms record000_result

certified_graph_case record001 16 28153384796160 GraphCoverageDescriptions.GraphCoverageBatch016.candidate01678 14

certified_graph_case record002 16 28168946253824 GraphCoverageDescriptions.GraphCoverageBatch016.candidate01679 14

certified_graph_case record003 16 28185245794304 GraphCoverageDescriptions.GraphCoverageBatch016.candidate01680 14

certified_graph_case record004 16 28214919495936 GraphCoverageDescriptions.GraphCoverageBatch016.candidate01681 14

certified_graph_case record005 16 28216459297024 GraphCoverageDescriptions.GraphCoverageBatch016.candidate01682 14

certified_graph_case record006 16 28232107687936 GraphCoverageDescriptions.GraphCoverageBatch016.candidate01683 14

certified_graph_case record007 16 28233139552256 GraphCoverageDescriptions.GraphCoverageBatch016.candidate01684 14

theorem record008_parameters : Parameters record008 (rowOfCode 16) 28233147875328 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record008_coverage : Coverage record008 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 28233147875328 :=
  GraphCoverageDescriptions.coverage_of_checked record008 GraphCoverageDescriptions.GraphCoverageBatch016.candidate01685 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 28233147875328
    (by rfl) record008_cells_exact
    (GraphCoverageDescriptions.small_allowed record008 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch016.candidate01685_checked

theorem record008_result : Result (16, 28233147875328) :=
  of_direct_small 16 28233147875328 (by decide) ⟨record008, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record008.direct_core, record008_parameters, record008_coverage⟩
#print axioms record008_result

certified_graph_case record009 16 28244868923648 GraphCoverageDescriptions.GraphCoverageBatch016.candidate01686 14

certified_graph_case record010 16 28244873085184 GraphCoverageDescriptions.GraphCoverageBatch016.candidate01687 14

certified_graph_case record011 16 28244873150464 GraphCoverageDescriptions.GraphCoverageBatch016.candidate01688 14

certified_graph_case record012 16 28244934983936 GraphCoverageDescriptions.GraphCoverageBatch016.candidate01689 14

certified_graph_case record013 16 28244939145472 GraphCoverageDescriptions.GraphCoverageBatch016.candidate01690 14

certified_graph_case record014 16 28244939210752 GraphCoverageDescriptions.GraphCoverageBatch016.candidate01691 14

certified_graph_case record015 16 28244942266624 GraphCoverageDescriptions.GraphCoverageBatch016.candidate01692 14

certified_graph_case record016 16 28245335507200 GraphCoverageDescriptions.GraphCoverageBatch016.candidate01693 14

certified_graph_case record017 16 28245335572480 GraphCoverageDescriptions.GraphCoverageBatch016.candidate01694 14

certified_graph_case record018 16 28248286757120 GraphCoverageDescriptions.GraphCoverageBatch016.candidate01695 14

certified_graph_case record019 16 28248294039808 GraphCoverageDescriptions.GraphCoverageBatch016.candidate01696 14

certified_graph_case record020 16 28248294105088 GraphCoverageDescriptions.GraphCoverageBatch016.candidate01697 14

certified_graph_case record021 16 28248311335168 GraphCoverageDescriptions.GraphCoverageBatch016.candidate01698 14

certified_graph_case record022 16 28248555225088 GraphCoverageDescriptions.GraphCoverageBatch016.candidate01699 14

certified_graph_case record023 16 28248558280960 GraphCoverageDescriptions.GraphCoverageBatch017.candidate01700 14

certified_graph_case record024 16 28248558346240 GraphCoverageDescriptions.GraphCoverageBatch017.candidate01701 14

certified_graph_case record025 16 28248566140960 GraphCoverageDescriptions.GraphCoverageBatch017.candidate01702 14

certified_graph_case record026 16 28256641286400 GraphCoverageDescriptions.GraphCoverageBatch017.candidate01703 14

certified_graph_case record027 16 28256649674752 GraphCoverageDescriptions.GraphCoverageBatch017.candidate01704 14

certified_graph_case record028 16 28257144021248 GraphCoverageDescriptions.GraphCoverageBatch017.candidate01705 14

certified_graph_case record029 16 28257152409600 GraphCoverageDescriptions.GraphCoverageBatch017.candidate01706 14

certified_graph_case record030 16 28257730887936 GraphCoverageDescriptions.GraphCoverageBatch017.candidate01707 14

certified_graph_case record031 16 28257739276288 GraphCoverageDescriptions.GraphCoverageBatch017.candidate01708 14

theorem record032_parameters : Parameters record032 (rowOfCode 16) 28265235415040 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record032_coverage : Coverage record032 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 28265235415040 :=
  GraphCoverageDescriptions.coverage_of_checked record032 GraphCoverageDescriptions.GraphCoverageBatch017.candidate01709 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 28265235415040
    (by rfl) record032_cells_exact
    (GraphCoverageDescriptions.small_allowed record032 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch017.candidate01709_checked

theorem record032_result : Result (16, 28265235415040) :=
  of_direct_small 16 28265235415040 (by decide) ⟨record032, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record032.direct_core, record032_parameters, record032_coverage⟩
#print axioms record032_result

certified_graph_case record033 16 28265465520384 GraphCoverageDescriptions.GraphCoverageBatch017.candidate01710 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029

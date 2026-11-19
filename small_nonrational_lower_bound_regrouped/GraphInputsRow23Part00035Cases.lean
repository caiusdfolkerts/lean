module
prelude
public meta import GraphCases
public import GraphInputsRow23Part00035Checked
public import GraphInputsRow23Part00035Metadata
public import GraphInputsRow23Part00035Frames
public import GraphInputsRow23Part00035Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch060
public import GraphCoverageBatch061
public import GraphInputsRow23Part00035Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 23 34498268905472 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06094 6

certified_graph_case record001 23 34498337046528 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06095 6

theorem record002_parameters : Parameters record002 (rowOfCode 23) 34498452652032 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record002_coverage : Coverage record002 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34498452652032 :=
  GraphCoverageDescriptions.coverage_of_checked record002 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06096 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 34498452652032
    (by rfl) record002_cells_exact
    (GraphCoverageDescriptions.small_allowed record002 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch060.candidate06096_checked

theorem record002_result : Result (23, 34498452652032) :=
  of_direct_small 23 34498452652032 (by decide) ⟨record002, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00035.record002.direct_core, record002_parameters, record002_coverage⟩
#print axioms record002_result

certified_graph_case record003 23 34500398694400 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06097 6

certified_graph_case record004 23 34531554115584 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06098 6

certified_graph_case record005 23 34531688316928 GraphCoverageDescriptions.GraphCoverageBatch060.candidate06099 6

certified_graph_case record006 23 34535832160256 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06100 6

certified_graph_case record007 23 34635707351296 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06101 6

certified_graph_case record008 23 34635725701376 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06102 6

certified_graph_case record009 23 34635744608256 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06103 6

certified_graph_case record010 23 34635752931328 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06104 6

certified_graph_case record011 23 34635759255808 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06105 6

certified_graph_case record012 23 34635975819264 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06106 6

certified_graph_case record013 23 34635984142336 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06107 6

certified_graph_case record014 23 34636495589376 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06108 6

certified_graph_case record015 23 34640022798336 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06109 6

certified_graph_case record016 23 34640295362560 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06110 6

certified_graph_case record017 23 34640790814720 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06111 6

certified_graph_case record018 23 34643760386048 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06112 6

certified_graph_case record019 23 34643776901120 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06113 6

certified_graph_case record020 23 34644850377216 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06114 6

certified_graph_case record021 23 34647535321088 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06115 6

theorem record022_parameters : Parameters record022 (rowOfCode 23) 34670188232704 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record022_coverage : Coverage record022 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34670188232704 :=
  GraphCoverageDescriptions.coverage_of_checked record022 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06116 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 34670188232704
    (by rfl) record022_cells_exact
    (GraphCoverageDescriptions.small_allowed record022 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch061.candidate06116_checked

theorem record022_result : Result (23, 34670188232704) :=
  of_direct_small 23 34670188232704 (by decide) ⟨record022, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00035.record022.direct_core, record022_parameters, record022_coverage⟩
#print axioms record022_result

certified_graph_case record023 23 34674621546496 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06117 6

theorem record024_parameters : Parameters record024 (rowOfCode 23) 34675150028800 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record024_coverage : Coverage record024 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 34675150028800 :=
  GraphCoverageDescriptions.coverage_of_checked record024 GraphCoverageDescriptions.GraphCoverageBatch061.candidate06118 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 6)) 34675150028800
    (by rfl) record024_cells_exact
    (GraphCoverageDescriptions.small_allowed record024 6 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch061.candidate06118_checked

theorem record024_result : Result (23, 34675150028800) :=
  of_direct_small 23 34675150028800 (by decide) ⟨record024, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00035.record024.direct_core, record024_parameters, record024_coverage⟩
#print axioms record024_result
end Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00035

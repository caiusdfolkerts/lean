module
prelude
public meta import GraphCases
public import GraphInputsRow26Part00078Checked
public import GraphInputsRow26Part00078Metadata
public import GraphInputsRow26Part00078Frames
public import GraphInputsRow26Part00078Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch103
public import GraphInputsRow26Part00078Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 26 32822693724672 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10318 14

certified_graph_case record001 26 32839319945732 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10319 14

certified_graph_case record002 26 32916646404352 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10320 14

certified_graph_case record003 26 32916713570304 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10321 14

certified_graph_case record004 26 32916721893376 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10322 14

certified_graph_case record005 26 32917183275008 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10323 14

certified_graph_case record006 26 32917233600512 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10324 14

theorem record007_parameters : Parameters record007 (rowOfCode 26) 32918776973568 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record007_coverage : Coverage record007 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32918776973568 :=
  GraphCoverageDescriptions.coverage_of_checked record007 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10325 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 32918776973568
    (by rfl) record007_cells_exact
    (GraphCoverageDescriptions.small_allowed record007 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch103.candidate10325_checked

theorem record007_result : Result (26, 32918776973568) :=
  of_direct_small 26 32918776973568 (by decide) ⟨record007, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00078.record007.direct_core, record007_parameters, record007_coverage⟩
#print axioms record007_result

certified_graph_case record008 26 32919313844224 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10326 14

certified_graph_case record009 26 32919330488832 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10327 14

theorem record010_parameters : Parameters record010 (rowOfCode 26) 32933809358880 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record010_coverage : Coverage record010 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 32933809358880 :=
  GraphCoverageDescriptions.coverage_of_checked record010 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10328 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 32933809358880
    (by rfl) record010_cells_exact
    (GraphCoverageDescriptions.small_allowed record010 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch103.candidate10328_checked

theorem record010_result : Result (26, 32933809358880) :=
  of_direct_small 26 32933809358880 (by decide) ⟨record010, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00078.record010.direct_core, record010_parameters, record010_coverage⟩
#print axioms record010_result

certified_graph_case record011 26 32935956709892 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10329 14

certified_graph_case record012 26 33022146003200 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10332 14

certified_graph_case record013 26 33025419182080 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10334 14

certified_graph_case record014 26 33058653217024 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10336 14

certified_graph_case record015 26 33063938621440 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10338 14

certified_graph_case record016 26 33064135696640 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10339 14

certified_graph_case record017 26 33098495492096 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10341 14

certified_graph_case record018 26 33102730625024 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10342 14

certified_graph_case record019 26 33126320455680 GraphCoverageDescriptions.GraphCoverageBatch103.candidate10343 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00078

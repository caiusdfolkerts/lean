module
prelude
public meta import GraphCases
public import GraphInputsRow31Part00083Checked
public import GraphInputsRow31Part00083Metadata
public import GraphInputsRow31Part00083Frames
public import GraphInputsRow31Part00083Leaves
public import GraphEmbeddingCoverage
public import GraphCoverageBatch162
public import GraphCoverageBatch163
public import GraphInputsRow31Part00083Structural000


@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00083
open Papers.RationalityTen PackedGraphCertificate SharedGraphCellPool
open GraphCaseCertificate GraphRowSpecifications

certified_graph_case record000 31 16774032588800 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16280 14

certified_graph_case record001 31 16774800605184 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16281 14

certified_graph_case record002 31 16778961354752 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16282 14

certified_graph_case record003 31 16785875173376 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16283 14

certified_graph_case record004 31 16786011455488 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16284 14

certified_graph_case record005 31 16786915360768 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16285 14

certified_graph_case record006 31 16823387062272 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16286 14

certified_graph_case record007 31 16907277238272 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16287 14

certified_graph_case record008 31 16930761081348 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16288 14

certified_graph_case record009 31 16930830286848 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16289 14

certified_graph_case record010 31 16943922806784 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16290 14

certified_graph_case record011 31 16952772788224 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16291 14

certified_graph_case record012 31 16965255036928 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16292 14

certified_graph_case record013 31 16969415786496 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16293 14

certified_graph_case record014 31 17043521306880 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16294 14

certified_graph_case record015 31 17043541786880 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16295 14

theorem record016_parameters : Parameters record016 (rowOfCode 31) 17043558563840 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record016_coverage : Coverage record016 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 17043558563840 :=
  GraphCoverageDescriptions.coverage_of_checked record016 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16296 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 17043558563840
    (by rfl) record016_cells_exact
    (GraphCoverageDescriptions.small_allowed record016 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch162.candidate16296_checked

theorem record016_result : Result (31, 17043558563840) :=
  of_direct_small 31 17043558563840 (by decide) ⟨record016, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00083.record016.direct_core, record016_parameters, record016_coverage⟩

theorem record017_parameters : Parameters record017 (rowOfCode 31) 17043566886912 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record017_coverage : Coverage record017 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 17043566886912 :=
  GraphCoverageDescriptions.coverage_of_checked record017 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16297 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 17043566886912
    (by rfl) record017_cells_exact
    (GraphCoverageDescriptions.small_allowed record017 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch162.candidate16297_checked

theorem record017_result : Result (31, 17043566886912) :=
  of_direct_small 31 17043566886912 (by decide) ⟨record017, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00083.record017.direct_core, record017_parameters, record017_coverage⟩

certified_graph_case record018 31 17043776667904 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16298 14

theorem record019_parameters : Parameters record019 (rowOfCode 31) 17043789774848 where
  kind_count := by decide +kernel
  quota := by decide +kernel
  required := by decide +kernel
  internal_missing := by decide +kernel
  minimum_incidence := by decide +kernel

theorem record019_coverage : Coverage record019 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows 17043789774848 :=
  GraphCoverageDescriptions.coverage_of_checked record019 GraphCoverageDescriptions.GraphCoverageBatch162.candidate16299 FacetUniverses.FullSmall.cells SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (GraphCoverageDescriptions.quota 14)) 17043789774848
    (by rfl) record019_cells_exact
    (GraphCoverageDescriptions.small_allowed record019 14 (by decide +kernel))
    GraphEmbeddingCoverage.small_edges GraphCoverageDescriptions.GraphCoverageBatch162.candidate16299_checked

theorem record019_result : Result (31, 17043789774848) :=
  of_direct_small 31 17043789774848 (by decide) ⟨record019, Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00083.record019.direct_core, record019_parameters, record019_coverage⟩

certified_graph_case record020 31 17043798097920 GraphCoverageDescriptions.GraphCoverageBatch163.candidate16300 14
end Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00083
